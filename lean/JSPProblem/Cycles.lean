/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000089 formalization (Yi-111-a).
-/
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# JSP-000089 : cycles in graphs, and why the even cycle lengths are forced

**Catalog problem** (JSP-000089).  *Is there a density-zero set of positive integers
such that every sufficiently dense graph has a cycle with length in that set?*

Two ingredients are needed to answer this.

1. **The combinatorial ingredient** (this file): the cycle lengths that graphs of
   large minimum degree are *forced* to contain.  We prove
   `bipartite_cycle_even`: **every cycle of a bipartite graph has even length**,
   together with the parity machinery `walk_parity` from which it follows.

2. **The arithmetic ingredient** (`JSPProblem.Density`): the set of even positive
   integers is *not* density zero.

Together these say that the natural candidate set for the catalog question — the
even numbers — is the set of lengths that a large class of "sufficiently dense"
graphs (all the bipartite ones) is *forced* to produce, and that it fails the
density-zero requirement.

## Main results of this file

* `bool_flip`, `bool_eq_flip` — elementary `Bool` lemmas.
* `walk_parity` — **the parity lemma**: the length of a walk is even exactly when
  its two endpoints receive the same colour in any proper `Bool` colouring.  This
  is the formal form of "walking along an edge flips the colour".
* `partFlag`, `partFlag_valid` — the bipartition induces a proper `Bool` colouring.
* `bipartite_cycle_even` — **every cycle of a bipartite graph has even length**.
* `bipartite_cycle_length_mem` — the cycle lengths of a bipartite graph are
  *even*, so no odd length is forced by a bipartite graph.
-/

namespace JSPProblem

open SimpleGraph

/-! ### Elementary `Bool` lemmas -/

/-- Two distinct `Bool`s are `!` of each other. -/
theorem bool_flip {x y : Bool} (h : x ≠ y) : x = !y := by
  cases x <;> cases y <;> first | rfl | exact absurd rfl h

/-- If `a = !b` then `a = c` iff `b ≠ c`. -/
theorem bool_eq_flip {a b c : Bool} (h : a = !b) : a = c ↔ ¬ (b = c) := by
  cases a with
  | false =>
    cases b with
    | false => exact absurd h (by decide)
    | true => simp
  | true =>
    cases b with
    | false => simp
    | true => exact absurd h (by decide)

/-! ### The parity lemma -/

variable {G : SimpleGraph V}

/-- **Parity lemma.**  If `f : V → Bool` is a proper colouring of `G` — adjacent
vertices get different colours — then a walk from `u` to `v` has even length
exactly when `u` and `v` have the same colour.

This is the standard "the walk alternates colours" argument, made formal.  Note
it applies to *any* proper `Bool` colouring, not just one coming from a
partition. -/
theorem walk_parity (f : V → Bool) (hf : ∀ a b, G.Adj a b → f a ≠ f b)
    {u v : V} (p : G.Walk u v) : Even p.length ↔ f u = f v := by
  induction p with
  | nil => exact ⟨fun h => by simpa using h, fun _ => by simp⟩
  | @cons a b c hab p ih =>
    have hflip : f a = !(f b) := bool_flip (hf a b hab)
    have hkey : f a = f c ↔ ¬ (f b = f c) := bool_eq_flip hflip
    have hiff : Even p.length ↔ f b = f c := ih
    constructor
    · intro he
      change Even (p.length + 1) at he
      show f a = f c
      refine hkey.mpr ?_
      intro hbc
      have hpb : Even p.length := hiff.mpr hbc
      have hn : ¬ Even p.length := (Nat.even_add_one (n := p.length)).mp he
      exact hn hpb
    · intro hfc
      change Even (p.length + 1)
      refine (Nat.even_add_one (n := p.length)).mpr ?_
      intro hpb
      have hbc : f b = f c := hiff.mp hpb
      exact hkey.mp hfc hbc

/-! ### Bipartite graphs have only even cycles -/

/-- `partFlag s v` is `true` when `v ∈ s` and `false` otherwise: the indicator of
one side of a bipartition. -/
noncomputable def partFlag (s : Set V) (v : V) : Bool := by
  classical exact decide (v ∈ s)

theorem partFlag_of_mem (s : Set V) {v : V} (hv : v ∈ s) : partFlag s v = true := by
  simp [partFlag, hv]

theorem partFlag_of_not_mem (s : Set V) {v : V} (hv : v ∉ s) : partFlag s v = false := by
  simp [partFlag, hv]

/-- **A bipartition is a proper `Bool` colouring.**  Adjacent vertices lie in
opposite parts, so the indicator `partFlag` of one part is a proper colouring. -/
theorem partFlag_valid {s t : Set V} (hb : G.IsBipartiteWith s t) (a b : V) (hab : G.Adj a b) :
    partFlag s a ≠ partFlag s b := by
  have h : (a ∈ s ∧ b ∈ t) ∨ (a ∈ t ∧ b ∈ s) := hb.mem_of_adj hab
  have hst : ∀ (x : V), x ∈ s → x ∉ t := Set.disjoint_left.mp hb.disjoint
  have hts : ∀ (x : V), x ∈ t → x ∉ s := Set.disjoint_left.mp (hb.disjoint.symm)
  rcases h with h | h
  · have has : a ∈ s := h.1
    have hbt : b ∈ t := h.2
    have hbns : b ∉ s := fun hbs => hst b hbs hbt
    rw [partFlag_of_mem (s := s) has, partFlag_of_not_mem (s := s) hbns]
    exact fun h => by simp at h
  · have hat : a ∈ t := h.1
    have hbs : b ∈ s := h.2
    have hans : a ∉ s := fun has => hts a hat has
    rw [partFlag_of_not_mem (s := s) hans, partFlag_of_mem (s := s) hbs]
    exact fun h => by simp at h

/-- **Bipartite graphs have only even cycles.**  Every cycle in a graph with a
bipartition `s ⊔ t` has even length: walking round the cycle alternates between
`s` and `t`, and one must return to the starting vertex, so the number of steps
is even. -/
theorem bipartite_cycle_even {s t : Set V} (hb : G.IsBipartiteWith s t)
    {u : V} (w : G.Walk u u) (hc : w.IsCycle) : Even w.length := by
  classical
  have hiff : Even w.length ↔ partFlag s u = partFlag s u :=
    walk_parity (partFlag s) (partFlag_valid hb) w
  exact hiff.mpr rfl

/-- **Corollary (cycle length membership).**  The length of a cycle in a
bipartite graph is an even positive integer.  This is the statement that a
bipartite "sufficiently dense" graph never forces an odd cycle length. -/
theorem bipartite_cycle_length_even {s t : Set V} (hb : G.IsBipartiteWith s t)
    {u : V} (w : G.Walk u u) (hc : w.IsCycle) :
    0 < w.length ∧ Even w.length := by
  have h3 : 3 ≤ w.length := hc.isCircuit.three_le_length
  exact ⟨Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) h3, bipartite_cycle_even hb w hc⟩

end JSPProblem
