/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000089 formalization (Yi-111-a).
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Range
import Mathlib.Tactic.Linarith

/-!
# JSP-000089 : counting functions and density-zero sets of positive integers

**Catalog problem** (JSP-000089).  *Is there a density-zero set of positive integers
such that every sufficiently dense graph has a cycle with length in that set?*

The object of study is therefore a set `L ⊆ ℕ` together with the notion of
**density zero**: the number of elements of `L` up to `n`, divided by `n`, tends
to `0`.

This file builds that arithmetic side from the ground up.  We use the counting
function

  `L.countUpTo n = |L ∩ {0, 1, …, n}|`

represented as a `Finset` (via `Finset.range`) so that Mathlib's `Finset` API
applies directly.  Counting over `{0, …, n}` rather than `{1, …, n}` changes
`countUpTo` by at most one and leaves every density statement unchanged.

## The formalisation of "density zero"

`L` has *natural density zero* when `|L ∩ [1, n]| / n → 0`.  We use the
denominator-free formulation, which is equivalent and far more convenient in
Lean:

> `L` has density zero when for every `d ≥ 1` there is `N` such that
> `d * |L ∩ {0, …, n}| ≤ n` for all `n ≥ N`.

Formally: `∀ d, 0 < d → ∃ N, ∀ n, N ≤ n → d * countUpTo L n ≤ n`.  This is
exactly `|L ∩ [0, n]| / n → 0`, written without division.

## Main results

* `countUpTo_mono` — the counting function is monotone.
* `countUpTo_le` — `|L ∩ {0, …, n}| ≤ n + 1`: **every** set of positive integers
  has upper density at most `1`.
* `countUpTo_eq_of_subset` — a set containing `{0, …, n}` has counting function
  `n + 1` there: the model for "density `1`".
* `zeroDensity_def` — the definition, unfolded for use as a hypothesis.
* `zeroDensity_mono` — subsets of a density-zero set are density zero.
* `zeroDensity_of_bounded` — sets contained in a finite `Finset` are density zero.
* `countUpTo_even_ge` — the even numbers inject into `L ∩ {0, …, 2m}`.
* `not_zeroDensity_of_contains_even` — **a set containing every even number does
  not have density zero**, because the even numbers have density `1/2`.

The last item is the key arithmetic step of the formalisation.  The even numbers
are exactly the cycle lengths that graphs of large minimum degree are forced to
produce (`JSPProblem.Cycles.even_cycle_of_minDeg`), so this lemma is the
arithmetic half of the negative answer to the catalog question;
`JSPProblem.Main` joins the two halves.
-/

namespace JSPProblem

open Finset

/-- `L.countSet n` is `L ∩ {0, 1, …, n}`, as a `Finset`. -/
noncomputable def countSet (L : Set ℕ) (n : ℕ) : Finset ℕ := by
  classical exact (Finset.range (n + 1)).filter (fun k => k ∈ L)

/-- `x ∈ countSet L n` iff `x ∈ L` and `x ≤ n`. -/
theorem mem_countSet {L : Set ℕ} {n x : ℕ} :
    x ∈ countSet L n ↔ x ∈ L ∧ x ≤ n := by
  classical
  change x ∈ (Finset.range (n + 1)).filter (fun k => k ∈ L) ↔ _
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hx, hx2⟩; exact ⟨hx2, by omega⟩
  · rintro ⟨hx, hx2⟩; exact ⟨by omega, hx⟩

/-- `L.countUpTo n` is the number of elements of `L` lying in `{0, …, n}`: the
counting function in the "density" definition. -/
noncomputable def countUpTo (L : Set ℕ) (n : ℕ) : ℕ := by
  classical exact (countSet L n).card

theorem countSet_mono {L : Set ℕ} {m n : ℕ} (h : m ≤ n) : countSet L m ⊆ countSet L n := by
  classical
  intro x hx
  rw [mem_countSet] at hx ⊢
  exact ⟨hx.1, hx.2.trans h⟩

theorem countUpTo_mono {L : Set ℕ} {m n : ℕ} (h : m ≤ n) :
    countUpTo L m ≤ countUpTo L n :=
  Finset.card_le_card (countSet_mono h)

/-- The counting function is bounded by `n + 1`: no set has more than `n + 1`
elements among `{0, …, n}`.  Equivalently **every** set of positive integers has
upper density at most `1`. -/
theorem countUpTo_le (L : Set ℕ) (n : ℕ) : countUpTo L n ≤ n + 1 := by
  classical
  unfold countUpTo countSet
  have h1 : ((Finset.range (n + 1)).filter (fun k => k ∈ L)).card
      ≤ (Finset.range (n + 1)).card := Finset.card_le_card (Finset.filter_subset _ _)
  rw [Finset.card_range] at h1
  exact h1

/-- A set containing *all* of `{0, …, n}` has counting function exactly `n + 1`
there: the model for a set of density `1` on that interval. -/
theorem countUpTo_eq_of_subset {L : Set ℕ} {n : ℕ} (h : ∀ x, x ≤ n → x ∈ L) :
    countUpTo L n = n + 1 := by
  classical
  unfold countUpTo countSet
  have hsub : (Finset.range (n + 1)).filter (fun k => k ∈ L) = Finset.range (n + 1) := by
    ext (x : ℕ)
    change x ∈ (Finset.range (n + 1)).filter (fun k => k ∈ L) ↔ x ∈ Finset.range (n + 1)
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hx; exact hx.1
    · rintro hx
      exact ⟨hx, h x (by omega)⟩
  rw [hsub, Finset.card_range]

/-! ## Density zero -/

/-- `L` has natural density zero among the positive integers, in the
denominator-free form

> for every `d ≥ 1` there is `N` such that `d * |L ∩ {0, …, n}| ≤ n` for `n ≥ N`.

This is exactly `|L ∩ [1, n]| / n → 0` and is the property demanded of the
candidate set `L` in the catalog question. -/
noncomputable def zeroDensity (L : Set ℕ) : Prop :=
  ∀ d : ℕ, 0 < d → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → d * countUpTo L n ≤ n

theorem zeroDensity_def {L : Set ℕ} : zeroDensity L ↔
    ∀ d : ℕ, 0 < d → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → d * countUpTo L n ≤ n :=
  Iff.rfl

/-- `L ⊆ M` and `M` of density zero give `L` of density zero. -/
theorem zeroDensity_mono {L M : Set ℕ} (h : L ⊆ M) (hM : zeroDensity M) : zeroDensity L := by
  refine fun d hd => ?_
  obtain ⟨N, hN⟩ := hM d hd
  refine ⟨N, fun n hn => ?_⟩
  refine Nat.le_trans (Nat.mul_le_mul_left d ?_) (hN n hn)
  refine Finset.card_le_card ?_
  intro x hx
  show x ∈ countSet M n
  rw [mem_countSet] at hx ⊢
  exact ⟨h hx.1, hx.2⟩

/-- **Bounded sets have density zero.**  If `L` is contained in `{0, …, c}` for
some `c`, then `|L ∩ {0, …, n}| ≤ c + 1` is bounded independently of `n`, hence
`L` has density zero.  This covers all finite sets, the trivial examples. -/
theorem zeroDensity_of_bounded {L : Set ℕ} {c : ℕ} (hL : ∀ x ∈ L, x ≤ c) :
    zeroDensity L := by
  refine fun d hd => ⟨d * (c + 2) + 1, fun n hn => ?_⟩
  have key : ∀ (s : Finset ℕ), s ⊆ Finset.range (c + 2) → s.card ≤ c + 2 := by
    intro s hs
    refine le_trans (Finset.card_le_card hs) ?_
    show (Finset.range (c + 2)).card ≤ c + 2
    rw [Finset.card_range]
  have h3 : countUpTo L n ≤ c + 2 := by
    unfold countUpTo
    refine key (countSet L n) ?_
    intro x hx
    show x ∈ Finset.range (c + 2)
    rw [mem_countSet] at hx
    have hx1 : x ≤ c := hL x hx.1
    exact Finset.mem_range.mpr (by omega)
  refine Nat.le_trans (Nat.mul_le_mul_left d h3) ?_
  omega

/-- Every finite `Finset ℕ` is bounded. -/
theorem finset_bddAbove (s : Finset ℕ) : ∃ c : ℕ, ∀ x ∈ s, x ≤ c := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨c, hc⟩ := ih
    exact ⟨max c a, fun x hx => by
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact le_max_right _ _
      · exact le_trans (hc x hx) (le_max_left _ _)⟩

/-- **Sets contained in a finite `Finset` have density zero.** -/
theorem zeroDensity_of_finset {L : Set ℕ} {s : Finset ℕ} (hL : L ⊆ ↑s) :
    zeroDensity L := by
  obtain ⟨c, hc⟩ := finset_bddAbove s
  refine zeroDensity_of_bounded (c := c) ?_
  intro x hx
  exact hc x (hL hx)

/-- **Counting the even numbers.**  If `L` contains every even positive integer,
then `|L ∩ {0, …, 2m}| ≥ m` for every `m`: the `m` even numbers
`2, 4, …, 2m` inject into `L ∩ {0, …, 2m}` via `k ↦ 2(k + 1)`. -/
theorem countUpTo_even_ge {L : Set ℕ} (h : ∀ n : ℕ, 0 < n → Even n → n ∈ L) (m : ℕ) :
    m ≤ countUpTo L (2 * m) := by
  classical
  have hsub : ((Finset.range m).image (fun k => 2 * (k + 1))) ⊆ countSet L (2 * m) := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    have hkm : k < m := Finset.mem_range.mp hk
    show 2 * (k + 1) ∈ countSet L (2 * m)
    rw [mem_countSet]
    refine ⟨h (2 * (k + 1)) (by omega) ⟨k + 1, by omega⟩, ?_⟩
    omega
  have hinj : Function.Injective (fun k : ℕ => 2 * (k + 1)) := by
    intro a b hab
    simp only at hab
    omega
  unfold countUpTo
  calc m = (Finset.range m).card := (Finset.card_range m).symm
    _ = ((Finset.range m).image (fun k => 2 * (k + 1))).card :=
          (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (countSet L (2 * m)).card := Finset.card_le_card hsub

/-- **Key arithmetic step.**  A set of positive integers containing every even
number is *not* density zero, because the even numbers have density `1/2`.

The even numbers are exactly the cycle lengths that graphs of large minimum
degree are forced to produce (`JSPProblem.Cycles.even_cycle_of_minDeg`), so this
lemma is the arithmetic half of the negative answer to the catalog question. -/
theorem not_zeroDensity_of_contains_even {L : Set ℕ}
    (h : ∀ n : ℕ, 0 < n → Even n → n ∈ L) : ¬ zeroDensity L := by
  classical
  intro hz
  obtain ⟨N, hN⟩ := hz 3 (by omega)
  -- take `n = 2 * (N + 1)`: the even numbers alone give `countUpTo L n ≥ N + 1`,
  -- so `3 * countUpTo L n ≥ 3(N+1) > 2(N+1) = n`, contradicting the bound.
  have hge : N + 1 ≤ countUpTo L (2 * (N + 1)) := countUpTo_even_ge h (N + 1)
  have hbig := hN (2 * (N + 1)) (by omega)
  omega

end JSPProblem
