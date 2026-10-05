import Algorithm

/-!
# Finite delay accounting

Generic weighted-disjointness lemmas for charging a comparator's delay cost:
request identifiers are assigned to payments, and disjoint assignments never
charge a request twice.
-/

namespace PagingWithDelay.Competitive

variable {Source Item : Type*} [DecidableEq Source] [DecidableEq Item]

def assignedUnion (sources : Finset Source) (assigned : Source → Finset Item) :
    Finset Item := sources.biUnion assigned

private theorem assigned_sum_eq_union_sum (weight : Item → Cost)
    (sources : Finset Source) (assigned : Source → Finset Item)
    (hdisjoint : ∀ left, left ∈ sources → ∀ right, right ∈ sources →
      left ≠ right → Disjoint (assigned left) (assigned right)) :
    (∑ source ∈ sources, ∑ item ∈ assigned source, weight item) =
      ∑ item ∈ assignedUnion sources assigned, weight item := by
  classical
  induction sources using Finset.induction_on with
  | empty => simp [assignedUnion]
  | @insert source rest hnot ih =>
      have hpair : ∀ right ∈ rest, Disjoint (assigned source) (assigned right) := by
        intro right hright
        exact hdisjoint source (by simp) right (by simp [hright]) (by
          intro heq; subst right; exact hnot hright)
      have hdisjUnion : Disjoint (assigned source) (rest.biUnion assigned) := by
        rw [Finset.disjoint_biUnion_right]
        exact hpair
      rw [Finset.sum_insert hnot]
      rw [ih (by
        intro left hleft right hright hne
        exact hdisjoint left (by simp [hleft]) right (by simp [hright]) hne)]
      unfold assignedUnion
      rw [Finset.biUnion_insert, Finset.sum_union hdisjUnion]

/-- If distinct sources receive disjoint item sets, every source receives
weight at least one, and all assigned items lie in `items`, then the number of
sources is at most the total item weight. -/
theorem card_le_sum_of_disjoint_unit_charges
    (sources : Finset Source) (items : Finset Item)
    (assigned : Source → Finset Item) (weight : Item → Cost)
    (hunit : ∀ source ∈ sources, 1 ≤ ∑ item ∈ assigned source, weight item)
    (hsub : ∀ source ∈ sources, assigned source ⊆ items)
    (hdisjoint : ∀ left, left ∈ sources → ∀ right, right ∈ sources →
      left ≠ right → Disjoint (assigned left) (assigned right)) :
    (sources.card : Cost) ≤ ∑ item ∈ items, weight item := by
  classical
  have hsource : (sources.card : Cost) ≤
      ∑ source ∈ sources, ∑ item ∈ assigned source, weight item := by
    simpa using Finset.sum_le_sum fun source hsource => hunit source hsource
  rw [assigned_sum_eq_union_sum weight sources assigned hdisjoint] at hsource
  apply hsource.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro item hitem
    obtain ⟨source, hsource, hitem⟩ := Finset.mem_biUnion.mp hitem
    exact hsub source hsource hitem
  · intro item _ _
    exact bot_le

namespace Schedule

variable {Page : Type*} [DecidableEq Page]

omit [DecidableEq Page] in private theorem mem_enumerateFrom_index
    {requests : List (Request Page)}
    {next : ℕ} {occurrence : Occurrence Page}
    (hmem : occurrence ∈ enumerateFrom next requests) :
    ∃ offset, ∃ hoffset : offset < requests.length,
      occurrence.id = next + offset ∧ requests[offset] = occurrence.request := by
  induction requests generalizing next with
  | nil => simp [enumerateFrom] at hmem
  | cons request rest ih =>
      simp only [enumerateFrom, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact ⟨0, by simp, by simp, rfl⟩
      · obtain ⟨offset, hoffset, hid, hrequest⟩ := ih htail
        refine ⟨offset + 1, by simp; omega, ?_, ?_⟩
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hid
        · simpa [List.getElem_cons_succ] using hrequest

omit [DecidableEq Page] in
/-- Stable identifiers assigned by `enumerate` are precisely the original
request-list positions. -/
theorem mem_enumerate_id_index {requests : List (Request Page)}
    {occurrence : Occurrence Page} (hmem : occurrence ∈ enumerate requests) :
    ∃ hid : occurrence.id < requests.length,
      requests[occurrence.id] = occurrence.request := by
  unfold enumerate at hmem
  obtain ⟨offset, hoffset, hid, hrequest⟩ :=
    mem_enumerateFrom_index hmem
  have hidEq : occurrence.id = offset := by simpa using hid
  subst offset
  exact ⟨hoffset, hrequest⟩

omit [DecidableEq Page] in
/-- Convenient bound-only projection of `mem_enumerate_id_index`. -/
theorem id_lt_of_mem_enumerate {requests : List (Request Page)}
    {occurrence : Occurrence Page} (hmem : occurrence ∈ enumerate requests) :
    occurrence.id < requests.length :=
  (mem_enumerate_id_index hmem).choose

/-- Comparator delay weight of a request position.  Values outside the finite
request sequence are zero, allowing class-D batches to be represented solely
by stable natural-number identifiers. -/
noncomputable def requestIdWeight (schedule : PagingWithDelay.Schedule Page)
    (input : Instance Page) (id : ℕ) : Cost :=
  if h : id < input.requests.length then schedule.requestCost input.requests[id]
  else 0

/-- An authentic occurrence's identifier weight is exactly the comparator
cost of that occurrence's request. -/
theorem requestIdWeight_eq_requestCost_of_mem_enumerate
    (schedule : PagingWithDelay.Schedule Page) (input : Instance Page)
    {occurrence : Occurrence Page}
    (hmem : occurrence ∈ enumerate input.requests) :
    requestIdWeight schedule input occurrence.id =
      schedule.requestCost occurrence.request := by
  obtain ⟨hid, hrequest⟩ := mem_enumerate_id_index hmem
  simp only [requestIdWeight, hid, dite_true]
  rw [hrequest]

theorem sum_requestIdWeight_range (schedule : PagingWithDelay.Schedule Page)
    (input : Instance Page) :
    (∑ id ∈ Finset.range input.requests.length,
      requestIdWeight schedule input id) = schedule.totalDelay input := by
  have aux : ∀ (requests : List (Request Page)),
      (∑ id ∈ Finset.range requests.length,
        if h : id < requests.length then schedule.requestCost requests[id] else 0) =
        (requests.map schedule.requestCost).sum := by
    intro requests
    induction requests using List.reverseRecOn with
    | nil => simp
    | append_singleton requests request ih =>
        simp only [List.length_append, List.length_singleton, List.map_append,
          List.map_singleton, List.sum_append, List.sum_singleton]
        rw [Finset.sum_range_succ]
        have hlen : requests.length < requests.length + 1 := by omega
        simp only [hlen, dite_true]
        have hlen' : requests.length < (requests ++ [request]).length := by simp
        have hlast : (requests ++ [request])[requests.length]'hlen' = request := by simp
        rw [hlast, ← ih]
        congr 1
        apply Finset.sum_congr rfl
        intro id hid
        have hidlt : id < requests.length := Finset.mem_range.mp hid
        simp only [hidlt, Nat.lt_succ_of_lt hidlt, dite_true]
        rw [List.getElem_append_left hidlt]
  exact aux input.requests

/-- Direct specialization of the generic charging lemma to the comparator's
request-position weights. -/
theorem card_le_totalDelay_of_disjoint_id_charges
    {Source : Type*} [DecidableEq Source]
    (schedule : PagingWithDelay.Schedule Page) (input : Instance Page)
    (sources : Finset Source) (assigned : Source → Finset ℕ)
    (hunit : ∀ source ∈ sources,
      1 ≤ ∑ id ∈ assigned source, requestIdWeight schedule input id)
    (hauthentic : ∀ source ∈ sources,
      assigned source ⊆ Finset.range input.requests.length)
    (hdisjoint : ∀ left, left ∈ sources → ∀ right, right ∈ sources →
      left ≠ right → Disjoint (assigned left) (assigned right)) :
    (sources.card : Cost) ≤ schedule.totalDelay input := by
  rw [← sum_requestIdWeight_range schedule input]
  exact card_le_sum_of_disjoint_unit_charges sources
    (Finset.range input.requests.length) assigned
    (requestIdWeight schedule input) hunit hauthentic hdisjoint

end Schedule

end PagingWithDelay.Competitive
