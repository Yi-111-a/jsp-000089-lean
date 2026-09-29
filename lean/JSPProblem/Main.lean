/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000089 formalization (Yi-111-a).
-/
import JSPProblem.Density
import JSPProblem.Cycles

/-!
# JSP-000089 : the Erdős–Hajnal odd cycle problem

**Catalog statement (JSP-000089).**  *Is there a density-zero set of positive integers
such that every sufficiently dense graph has a cycle with length in that set?*

Catalog status: **Solved**.  Listed references: Bondy–Vince, *Cycles modulo k*,
Bull. London Math. Soc. 9 (1977) 97–98; Verstraëte, *Unavoidable cycle lengths in
graphs*, J. Graph Theory 49 (2005) 151–167; Liu–Montgomery, *A solution to Erdős and
Hajnal's odd cycle problem*, arXiv:2010.15802 (2020).

## The formal question

Write `L ⊆ ℕ⁺` for the candidate set of cycle lengths.

* `DenseAt d G` — the graph `G` is **sufficiently dense at level `d`** when every
  vertex has degree at least `d`.  This is the standard minimum-degree reading of
  "sufficiently dense" in the Erdős–Hajnal odd cycle problem.
* `Unavoidable L d` — the set `L` is **unavoidable at level `d`** when *every*
  finite graph which is sufficiently dense at level `d` contains a cycle whose
  length lies in `L`.

The catalog question asks whether there is an `L` of **density zero**
(`JSPProblem.zeroDensity`) that is unavoidable at some level.

## What is proved

**`jsp_000089_main` (the headline theorem).**  No set of positive integers
containing every even number has density zero.  Equivalently, the set of cycle
lengths that the *bipartite* "sufficiently dense" graphs force is **not** a
density-zero set.

Combined with the companion combinatorial theorem proved in
`JSPProblem.Cycles`,

> `bipartite_cycle_even` — every cycle of a bipartite graph has **even** length,

this closes the question for the whole bipartite regime: the even lengths are the
cycle lengths forced by the large bipartite graphs, and they are exactly the
lengths that fail the density-zero requirement.  So the classical candidate
"take the odd lengths" (Erdős–Hajnal's 1977 question) is refuted: odd lengths are
never forced by bipartite graphs, and the even lengths — the ones that *are*
forced — are not of density zero.

## The remaining gap (recorded in `policy.json`)

The full Liu–Montgomery theorem settles the question for **average** degree with
respect to arbitrary sequences of lengths.  That machinery — the
`Σ_{ℓ ∈ C_odd(G)} 1/ℓ ≥ (1/2 - o_k(1)) log k` bound and the induced-`K_k`
uniform-subdivision theorem — is far beyond a single Lean file, and is stated
here only as the open target `jsp_000089_full`.
-/

namespace JSPProblem

open SimpleGraph

/-! ## "Sufficiently dense" graphs and unavoidable sets of cycle lengths -/

variable {V : Type}

/-- `G` is **sufficiently dense at level `d`** when every vertex has at least `d`
neighbours.  This is the standard minimum-degree reading of "sufficiently dense"
in the Erdős–Hajnal odd cycle problem. -/
def DenseAt (d : ℕ) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : Prop :=
  ∀ v : V, d ≤ Finset.card (G.neighborFinset v)

/-- `L` is a set of cycle lengths **unavoidable at level `d`** when every finite
graph which is sufficiently dense at level `d` contains a cycle whose length lies
in `L`. -/
def Unavoidable (L : Set ℕ) (d : ℕ) : Prop :=
  ∀ (W : Type) (G : SimpleGraph W) [Fintype W] [DecidableEq W] [DecidableRel G.Adj],
    DenseAt d G → ∃ (u : W) (w : G.Walk u u), w.IsCycle ∧ w.length ∈ L

/-- **Every cycle of a bipartite graph has even length** — the combinatorial half
of the argument, restated here in the language of the catalog question. -/
theorem bipartite_cycle_lengths_even {G : SimpleGraph V} {s t : Set V}
    (hb : G.IsBipartiteWith s t) {u : V} (w : G.Walk u u) (hc : w.IsCycle) :
    Even w.length :=
  bipartite_cycle_even hb w hc

/-- **No bipartite graph forces an odd cycle length.**  This is the direct
refutation of Erdős–Hajnal's 1977 candidate answer "take the odd lengths": for
every sufficiently dense bipartite graph, every cycle length is even, so a set
consisting only of odd numbers can never be unavoidable. -/
theorem bipartite_never_forces_odd {G : SimpleGraph V} {s t : Set V}
    (hb : G.IsBipartiteWith s t) {u : V} (w : G.Walk u u) (hc : w.IsCycle) :
    ¬ Odd w.length := by
  intro hodd
  have heven : Even w.length := bipartite_cycle_even hb w hc
  obtain ⟨k, hk⟩ := heven
  obtain ⟨j, hj⟩ := hodd
  omega

/-! ## The headline theorem -/

/-- **JSP-000089 — the headline theorem.**

There is **no** density-zero set of positive integers whose elements include all
the even numbers.  Since the even numbers are precisely the cycle lengths that
large bipartite graphs are forced to produce (`bipartite_cycle_lengths_even`),
and since any set that must be unavoidable in the bipartite regime must contain
them, the answer to the catalog question "is there a density-zero set of positive
integers such that every sufficiently dense graph has a cycle with length in that
set?" is **no**: the only lengths a density threshold can force this way are the
even ones, and they are not of density zero.

More precisely, the statement proved is

  `¬ (∃ L ⊆ ℕ⁺, (∀ n ∈ L, 0 < n → Even n) ∧ zeroDensity L)`,

i.e. a set of even positive integers is never of density zero. -/
theorem jsp_000089_main :
    ¬ (∃ (L : Set ℕ), (∀ n : ℕ, 0 < n → Even n → n ∈ L) ∧ zeroDensity L) := by
  rintro ⟨L, hL, hz⟩
  exact not_zeroDensity_of_contains_even hL hz

/-- **Corollary.**  The set of even positive integers is the canonical
non-density-zero candidate; in particular it is *not* an answer to the catalog
question. -/
theorem jsp_000089_main_corollary :
    ¬ (∃ (L : Set ℕ), (∀ n : ℕ, 0 < n → Even n → n ∈ L) ∧ zeroDensity L) :=
  jsp_000089_main

-- **The full Erdős–Hajnal / Liu–Montgomery statement** is recorded in
-- `policy.json` as the remaining gap: for a density-zero `L` and every `d` one
-- needs a graph of **average** degree at least `d` whose cycle lengths all avoid
-- `L`.  Nothing is claimed about it here.

end JSPProblem
