import Theorems.Thm_StickyKakeya4_finite_cover_profile_epochs

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

namespace FiniteCellLabelReduction

open DisjointProfileEpochs FiniteCoverProfileEpochs
open scoped BigOperators

variable {α β I : Type*} [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype I]

/-- Only the label space is reduced. Every original point and scale is unchanged. -/
def labelSet (cell : I → α → β) : Finset β :=
  Finset.univ.biUnion (fun i => Finset.univ.image (cell i))

abbrev Label (cell : I → α → β) := {b : β // b ∈ labelSet cell}

instance labelFintype (cell : I → α → β) : Fintype (Label cell) := inferInstance

omit [DecidableEq α] in
lemma cell_mem_labelSet (cell : I → α → β) (i : I) (a : α) : cell i a ∈ labelSet cell := by
  classical
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
    Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩

def reducedCell (cell : I → α → β) (i : I) (a : α) : Label cell :=
  ⟨cell i a, cell_mem_labelSet cell i a⟩

omit [DecidableEq α] in
@[simp] lemma reducedCell_val (cell : I → α → β) (i : I) (a : α) :
    (reducedCell cell i a).val = cell i a := rfl

omit [DecidableEq α] in
lemma label_projection_injective (cell : I → α → β) :
    Function.Injective (fun b : Label cell => b.val) := Subtype.val_injective

omit [DecidableEq α] in
lemma image_recover (cell : I → α → β) (i : I) (E : Finset α) :
    (E.image (reducedCell cell i)).image Subtype.val = E.image (cell i) := by
  rw [Finset.image_image]
  rfl

omit [DecidableEq α] in
lemma image_card_eq (cell : I → α → β) (i : I) (E : Finset α) :
    (E.image (reducedCell cell i)).card = (E.image (cell i)).card := by
  calc
    (E.image (reducedCell cell i)).card =
        ((E.image (reducedCell cell i)).image Subtype.val).card :=
      (Finset.card_image_of_injective _ (label_projection_injective cell)).symm
    _ = (E.image (cell i)).card := congrArg Finset.card (image_recover cell i E)

lemma coverCount_eq (cell : I → α → β) (i : I) (E W : Finset α) :
    coverCount (reducedCell cell i) E W = coverCount (cell i) E W :=
  image_card_eq cell i (E ∩ W)

lemma profile_eq (tubes : I → Finset (Finset α)) (cell : I → α → β)
    (i : I) (E : Finset α) :
    profile tubes (reducedCell cell) i E = profile tubes cell i E := by
  unfold profile
  congr 1
  funext W
  exact coverCount_eq cell i E W

lemma wholeCells_eq (cell : I → α → β) (i : I) (E W : Finset α) :
    wholeCells (reducedCell cell i) E W = wholeCells (cell i) E W := by
  classical
  ext a
  simp only [FiniteCoverProfileEpochs.mem_wholeCells]
  constructor
  · rintro ⟨ha, b, hb, heq⟩
    exact ⟨ha, b, hb, congrArg Subtype.val heq⟩
  · rintro ⟨ha, b, hb, heq⟩
    exact ⟨ha, b, hb, Subtype.ext heq⟩

omit [DecidableEq α] in
lemma gridCells_eq (cell : I → α → β) (i : I) (b : Label cell) :
    gridCells (reducedCell cell) (i, b) = gridCells cell (i, b.val) := by
  classical
  ext a
  simp only [gridCells, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Subtype.ext_iff

lemma population_eq (cell : I → α → β) (i : I) (b : Label cell) (E : Finset α) :
    population (gridCells (reducedCell cell)) E (i, b) =
      population (gridCells cell) E (i, b.val) := by
  simp only [population, gridCells_eq]

omit [Fintype I] in
lemma occupied_iff_mem_image (cell : I → α → β) (i : I) (b : β) (E : Finset α) :
    (population (gridCells cell) E (i, b)).Nonempty ↔ b ∈ E.image (cell i) := by
  rw [population_gridCells]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨haE, heq⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_image.mpr ⟨a, haE, heq⟩
  · rintro hb
    obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hb
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, heq⟩⟩

lemma regular_iff (cell : I → α → β) (threshold : I → ℕ) (E : Finset α) :
    Regular (gridCells (reducedCell cell)) (fun j => threshold j.1) E ↔
      Regular (gridCells cell) (fun j => threshold j.1) E := by
  constructor
  · intro h j hoccupied
    rcases j with ⟨i, b⟩
    have hb : b ∈ labelSet cell := by
      obtain ⟨a, _, heq⟩ := Finset.mem_image.mp
        ((occupied_iff_mem_image cell i b E).mp hoccupied)
      rw [← heq]
      exact cell_mem_labelSet cell i a
    let b' : Label cell := ⟨b, hb⟩
    have hpop : population (gridCells (reducedCell cell)) E (i, b') =
        population (gridCells cell) E (i, b) := population_eq cell i b' E
    have hr := h (i, b') (by rwa [hpop])
    rwa [hpop] at hr
  · intro h j hoccupied
    rcases j with ⟨i, b⟩
    have hpop := population_eq cell i b E
    have hr := h (i, b.val) (by rwa [← hpop])
    rwa [← hpop] at hr

/-- The raw penalty has a finite domain even when β is an infinite grid. -/
def rawPenalty (cell : I → α → β) (threshold : I → ℕ) (E : Finset α) : ℕ :=
  ∑ i : I, (E.image (cell i)).card * threshold i

lemma finite_penalty_eq [Fintype β] (cell : I → α → β) (threshold : I → ℕ)
    (E : Finset α) :
    penalty (gridCells cell) (fun j => threshold j.1) E = rawPenalty cell threshold E := by
  classical
  unfold penalty rawPenalty
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [occupied_iff_mem_image]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.univ : Finset β).filter (fun b => b ∈ E.image (cell i)) =
      E.image (cell i) := by ext b; simp
  rw [hfilter]
  simp

/-- Exact occupied-cell charging: unused labels add no cost, at any scale. -/
lemma reduced_penalty_eq (cell : I → α → β) (threshold : I → ℕ) (E : Finset α) :
    penalty (gridCells (reducedCell cell)) (fun j => threshold j.1) E =
      rawPenalty cell threshold E := by
  rw [finite_penalty_eq]
  unfold rawPenalty
  simp only [image_card_eq]

lemma maximizingFiber_iff (tubes : I → Finset (Finset α)) (cell : I → α → β)
    (threshold : I → ℕ) (i : I) (E F : Finset α) :
    MaximizingFiber tubes (reducedCell cell) threshold i E F ↔
      MaximizingFiber tubes cell threshold i E F := by
  simp only [MaximizingFiber, coverCount_eq, profile_eq, wholeCells_eq]

lemma concreteRule_iff (select : Finset α → I) (tubes : I → Finset (Finset α))
    (cell : I → α → β) (threshold : I → ℕ) (i : I) (A E F : Finset α) :
    ConcreteRule select tubes (reducedCell cell) threshold i A E F ↔
      ConcreteRule select tubes cell threshold i A E F := by
  simp only [ConcreteRule, maximizingFiber_iff]

lemma validEpoch_iff (select : Finset α → I) (tubes : I → Finset (Finset α))
    (cell : I → α → β) (threshold : I → ℕ) (K : ℕ) (e : Epoch α I) :
    ValidEpoch (gridCells (reducedCell cell)) (fun j => threshold j.1) K
        (profile tubes (reducedCell cell)) (ConcreteRule select tubes (reducedCell cell) threshold) e ↔
      ValidEpoch (gridCells cell) (fun j => threshold j.1) K
        (profile tubes cell) (ConcreteRule select tubes cell threshold) e := by
  simp only [ValidEpoch, profile_eq, regular_iff, concreteRule_iff]

/-- The native endpoint permits infinite raw labels, including literal integer
grid vectors. Every returned point and footprint is in its original space. -/
theorem exists_large_raw_label_epoch
    (tubes : I → Finset (Finset α)) (cell : I → α → β)
    (coverage : Covers tubes) (threshold : I → ℕ)
    (select : Finset α → I) (K : ℕ) (hK : 1 < K) (A : Finset α)
    (hbudget : rawPenalty cell threshold A < A.card) :
    ∃ e : Epoch α I,
      e.start ⊆ A ∧ e.index = select e.start ∧
      ValidEpoch (gridCells cell) (fun j => threshold j.1) K (profile tubes cell)
        (ConcreteRule select tubes cell threshold) e ∧
      (∀ F ∈ e.pieces, F.Nonempty) ∧ e.pieces.Pairwise Disjoint ∧
      (∀ F ∈ e.pieces, threshold e.index * profile tubes cell e.index e.start ≤ K * F.card) ∧
      support e.pieces ⊆ A ∧
      A.card ≤ (Fintype.card I * rank K A.card) * (support e.pieces).card +
        rawPenalty cell threshold A := by
  have hfinite : penalty (gridCells (reducedCell cell)) (fun j => threshold j.1) A < A.card := by
    rwa [reduced_penalty_eq]
  obtain ⟨e, hsub, hselected, hvalid, hnonempty, hdisjoint, hrich, hsupport, hmass⟩ :=
    exists_large_finite_cover_epoch tubes (reducedCell cell) coverage threshold select K hK A hfinite
  refine ⟨e, hsub, hselected,
    (validEpoch_iff select tubes cell threshold K e).mp hvalid, hnonempty, hdisjoint, ?_, hsupport, ?_⟩
  · simpa only [profile_eq] using hrich
  · simpa only [reduced_penalty_eq] using hmass

end FiniteCellLabelReduction
