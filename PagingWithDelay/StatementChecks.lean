import PagingWithDelay

/-!
# The public statements say what their earlier phrasings said

Two of the public theorems restrict the page universe. They state that
restriction as a bound on `Instance.pageUniverse`, the set of pages an input
actually requests, where earlier they carried a `Finset Page` of size `k + 1`
together with the hypothesis that every request lies in it. The general lower
bound also asks for `Algorithm.Feasible` in place of a feasibility hypothesis
written out over all inputs.

The examples below derive the earlier phrasings from the current ones, so both
changes are changes of phrasing only, and check that the hypotheses on an
algorithm are satisfiable at all. Like `OnlineExamples.lean`, this file is a
check on the statements rather than part of the development; build it with
`lake build PagingWithDelay.StatementChecks`.
-/

namespace PagingWithDelay

/-- The `k+1`-page upper bound still covers every input drawn from a named
universe of exactly `k + 1` pages. -/
example {Page : Type*} [DecidableEq Page] {k : ℕ} (hk : 0 < k) :
    ∃ (algorithm : Algorithm Page), Algorithm.Online algorithm ∧
      ∀ (input : Instance Page) (valid : input.Valid) (pages : Finset Page),
        input.cacheSize = k → pages.card = k + 1 →
        (∀ request ∈ input.requests, request.page ∈ pages) →
          (algorithm input valid).Feasible input ∧
            ∀ comparator : Schedule Page, comparator.Feasible input →
              (algorithm input valid).totalCost input ≤
                (2 * k + 1 : ℕ) * comparator.totalCost input +
                  ((2 * k + 1 : ℕ) * (2 * k + 1 : ℕ)) / (k : ℕ) := by
  obtain ⟨algorithm, online, competitive⟩ :=
    paging_with_delay_upper_bound_k_plus_one_pages (Page := Page) hk
  refine ⟨algorithm, online, fun input valid pages hsize hcard hrequests => ?_⟩
  exact competitive input valid
    (((pages.equivFinOfCardEq hcard).symm.toEmbedding).trans (Function.Embedding.subtype _))
    hsize ((Instance.card_pageUniverse_le hrequests).trans_eq hcard)

/-- The general lower bound still applies to an algorithm whose feasibility is
given input by input, and still produces an input drawn from a universe of
exactly `k + 1` pages. -/
example {Page : Type*} [DecidableEq Page] {k : ℕ} (hk : 0 < k) (pages : Fin (k + 1) ↪ Page)
    (algorithm : Algorithm Page) (online : Algorithm.Online algorithm)
    (feasible : ∀ (input : Instance Page) (valid : input.Valid),
      (algorithm input valid).Feasible input)
    (ratio additive : Cost) (hratio : ratio < (2 * k + 1 : ℕ)) :
    ∃ (input : Instance Page) (valid : input.Valid) (comparator : Schedule Page),
      input.cacheSize = k ∧
      (∃ cover : Finset Page, cover.card = k + 1 ∧
        ∀ request ∈ input.requests, request.page ∈ cover) ∧
      comparator.Feasible input ∧
        ratio * comparator.totalCost input + additive <
          (algorithm input valid).totalCost input := by
  obtain ⟨input, valid, comparator, hsize, huniverse, hfeasible, hcost⟩ :=
    paging_with_delay_general_lower_bound hk pages algorithm online ⟨feasible⟩ ratio additive
      hratio
  exact ⟨input, valid, comparator, hsize, input.exists_universe_card_eq pages huniverse,
    hfeasible, hcost⟩

/-- The hypotheses the general lower bound puts on an algorithm are satisfiable:
FIFO with threshold `1` is both online and feasible. -/
example {Page : Type*} [DecidableEq Page] :
    Algorithm.Online (FIFO.schedule (Page := Page) 1) ∧
      Algorithm.Feasible (FIFO.schedule (Page := Page) 1) :=
  ⟨FIFO.schedule_online 1, ⟨fun input valid => FIFO.schedule_feasible 1 input valid⟩⟩

end PagingWithDelay
