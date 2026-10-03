import Theorems.Thm_StickyKakeya4_disjoint_profile_epochs

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

namespace FiniteCoverProfileEpochs

open DisjointProfileEpochs
open scoped BigOperators

variable {α β I : Type*} [DecidableEq α] [DecidableEq β]

/-- Number of actual occupied cells met by a footprint. -/
def coverCount (cell : α → β) (E W : Finset α) : ℕ := ((E ∩ W).image cell).card

/-- The literal finite maximum over the supplied tube footprints. -/
def profile (tubes : I → Finset (Finset α)) (cell : I → α → β)
    (i : I) (E : Finset α) : ℕ :=
  (tubes i).sup (coverCount (cell i) E)

def Covers (tubes : I → Finset (Finset α)) : Prop :=
  ∀ i a, ∃ W ∈ tubes i, a ∈ W

lemma coverCount_mono (cell : α → β) {E D : Finset α} (h : E ⊆ D) (W : Finset α) :
    coverCount cell E W ≤ coverCount cell D W :=
  Finset.card_le_card (Finset.image_subset_image (Finset.inter_subset_inter_right h))

lemma profile_mono (tubes : I → Finset (Finset α)) (cell : I → α → β) (i : I) :
    Monotone (profile tubes cell i) := by
  intro E D h
  apply Finset.sup_le
  intro W hW
  exact (coverCount_mono (cell i) h W).trans (Finset.le_sup hW)

@[simp] lemma profile_empty (tubes : I → Finset (Finset α)) (cell : I → α → β) (i : I) :
    profile tubes cell i ∅ = 0 := by
  simp [profile, coverCount]

lemma profile_le_card (tubes : I → Finset (Finset α)) (cell : I → α → β)
    (i : I) (E : Finset α) : profile tubes cell i E ≤ E.card := by
  apply Finset.sup_le
  intro W _
  exact Finset.card_image_le.trans (Finset.card_le_card Finset.inter_subset_left)

lemma profile_positive (tubes : I → Finset (Finset α)) (cell : I → α → β)
    (coverage : Covers tubes) (i : I) (E : Finset α) (hE : E.Nonempty) :
    0 < profile tubes cell i E := by
  obtain ⟨a, ha⟩ := hE
  obtain ⟨W, hW, haW⟩ := coverage i a
  have hcount : 0 < coverCount (cell i) E W := by
    apply Finset.card_pos.mpr
    exact ⟨cell i a, Finset.mem_image.mpr ⟨a, Finset.mem_inter.mpr ⟨ha, haW⟩, rfl⟩⟩
  exact lt_of_lt_of_le hcount (Finset.le_sup hW)

/-- An attaining footprint is constructed from the actual finite family. -/
theorem exists_maximizing_footprint (tubes : I → Finset (Finset α))
    (cell : I → α → β) (coverage : Covers tubes) (i : I)
    (E : Finset α) (hE : E.Nonempty) :
    ∃ W ∈ tubes i, coverCount (cell i) E W = profile tubes cell i E ∧
      (E ∩ W).Nonempty := by
  have hEcopy := hE
  obtain ⟨a, _⟩ := hEcopy
  obtain ⟨W₀, hW₀, _⟩ := coverage i a
  obtain ⟨W, hW, hmax⟩ := Finset.exists_mem_eq_sup (tubes i) ⟨W₀, hW₀⟩
    (coverCount (cell i) E)
  have hpos := profile_positive tubes cell coverage i E hE
  refine ⟨W, hW, hmax.symm, ?_⟩
  have hcount : 0 < ((E ∩ W).image (cell i)).card := by
    change 0 < coverCount (cell i) E W
    rw [← hmax]
    exact hpos
  exact Finset.image_nonempty.mp (Finset.card_pos.mp hcount)

omit [DecidableEq β] in
lemma mem_wholeCells (cell : α → β) (E W : Finset α) (a : α) :
    a ∈ wholeCells cell E W ↔ a ∈ E ∧ ∃ b ∈ E ∩ W, cell a = cell b := by
  classical
  simp [wholeCells]

/-- Whole-cell expansion introduces exactly the same fine cells. -/
lemma wholeCells_image (cell : α → β) (E W : Finset α) :
    (wholeCells cell E W).image cell = (E ∩ W).image cell := by
  classical
  apply Finset.Subset.antisymm
  · intro b hb
    obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hb
    obtain ⟨_, d, hd, had⟩ := (mem_wholeCells cell E W a).mp ha
    exact Finset.mem_image.mpr ⟨d, hd, had.symm.trans hab⟩
  · exact Finset.image_subset_image (inter_subset_wholeCells cell E W)

/-- The exact equality also holds for every coarser label that factors through
this cell map; no extra ancestors are created by whole-cell expansion. -/
lemma wholeCells_image_ancestor {γ : Type*} [DecidableEq γ]
    (cell : α → β) (ancestor : β → γ) (E W : Finset α) :
    (wholeCells cell E W).image (ancestor ∘ cell) = (E ∩ W).image (ancestor ∘ cell) := by
  rw [← Finset.image_image, wholeCells_image, Finset.image_image]

lemma wholeCells_filter_eq (cell : α → β) (E W : Finset α) (b : β)
    (hb : b ∈ (E ∩ W).image cell) :
    (wholeCells cell E W).filter (fun a => cell a = b) = E.filter (fun a => cell a = b) := by
  classical
  obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hb
  apply Finset.Subset.antisymm
  · exact Finset.filter_subset_filter _ (wholeCells_subset cell E W)
  · intro x hx
    obtain ⟨hxE, hxb⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr
      ⟨(mem_wholeCells cell E W x).mpr ⟨hxE, a, ha, hxb.trans hab.symm⟩, hxb⟩

omit [DecidableEq α] in
lemma card_lt_pow_rank {K : ℕ} (hK : 1 < K) (A : Finset α) :
    A.card < K ^ rank K A.card := by
  by_cases hA : A.card = 0
  · simp [hA]
  · simpa [rank, hA] using Nat.lt_pow_succ_log_self hK A.card

lemma profile_lt_pow_rank {K : ℕ} (hK : 1 < K)
    (tubes : I → Finset (Finset α)) (cell : I → α → β) (A : Finset α) (i : I) :
    profile tubes cell i A < K ^ rank K A.card :=
  (profile_le_card tubes cell i A).trans_lt (card_lt_pow_rank hK A)

section OriginalFinitePoints

variable [Fintype α]

/-- The actual original spatial cells, with one index per scale and cell label. -/
def gridCells (cell : I → α → β) (j : I × β) : Finset α :=
  Finset.univ.filter (fun a => cell j.1 a = j.2)

lemma population_gridCells (cell : I → α → β) (E : Finset α) (i : I) (b : β) :
    population (gridCells cell) E (i, b) = E.filter (fun a => cell i a = b) := by
  ext a
  simp [population, gridCells]

/-- Richness is obtained by summing actual populations of disjoint cells,
rather than assumed as a property of an extracted family. -/
theorem wholeCells_card_ge (cell : I → α → β) (threshold : I → ℕ)
    (E W : Finset α) (i : I)
    (hregular : Regular (gridCells cell) (fun j => threshold j.1) E) :
    threshold i * coverCount (cell i) E W ≤ (wholeCells (cell i) E W).card := by
  classical
  let F := wholeCells (cell i) E W
  have himage : F.image (cell i) = (E ∩ W).image (cell i) := wholeCells_image (cell i) E W
  have hlower : ∀ b ∈ F.image (cell i), threshold i ≤ (F.filter (fun a => cell i a = b)).card := by
    intro b hb
    have hb' : b ∈ (E ∩ W).image (cell i) := by rwa [← himage]
    obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hb'
    have hpop : (population (gridCells cell) E (i, b)).Nonempty := by
      rw [population_gridCells]
      exact ⟨a, Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp ha).1, hab⟩⟩
    have hr := hregular (i, b) hpop
    rw [population_gridCells] at hr
    change threshold i ≤ ((wholeCells (cell i) E W).filter (fun a => cell i a = b)).card
    rw [wholeCells_filter_eq (cell i) E W b hb']
    exact hr
  calc
    threshold i * coverCount (cell i) E W = ∑ _b ∈ F.image (cell i), threshold i := by
      simp [himage, coverCount, Nat.mul_comm]
    _ ≤ ∑ b ∈ F.image (cell i), (F.filter (fun a => cell i a = b)).card :=
      Finset.sum_le_sum hlower
    _ = F.card := (Finset.card_eq_sum_card_image (cell i) F).symm

/-- With floor thresholds, occupied cells still contribute at least half their
real threshold, including when the natural floor is zero. -/
theorem wholeCells_card_ge_half_real (cell : I → α → β) (threshold : I → ℝ)
    (E W : Finset α) (i : I)
    (hregular : Regular (gridCells cell) (fun j => ⌊threshold j.1⌋₊) E) :
    (threshold i / 2) * (coverCount (cell i) E W : ℝ) ≤
      ((wholeCells (cell i) E W).card : ℝ) := by
  classical
  let F := wholeCells (cell i) E W
  have himage : F.image (cell i) = (E ∩ W).image (cell i) := wholeCells_image (cell i) E W
  have hlower : ∀ b ∈ F.image (cell i), threshold i / 2 ≤
      ((F.filter (fun a => cell i a = b)).card : ℝ) := by
    intro b hb
    have hb' : b ∈ (E ∩ W).image (cell i) := by rwa [← himage]
    obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hb'
    have hpop : (population (gridCells cell) E (i, b)).Nonempty := by
      rw [population_gridCells]
      exact ⟨a, Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp ha).1, hab⟩⟩
    have hr := hregular.half_real_threshold (i, b) hpop
    rw [population_gridCells] at hr
    change threshold i / 2 ≤
      (((wholeCells (cell i) E W).filter (fun a => cell i a = b)).card : ℝ)
    rw [wholeCells_filter_eq (cell i) E W b hb']
    exact hr
  calc
    (threshold i / 2) * (coverCount (cell i) E W : ℝ) =
        ∑ _b ∈ F.image (cell i), threshold i / 2 := by
      simp [himage, coverCount, mul_comm]
    _ ≤ ∑ b ∈ F.image (cell i), ((F.filter (fun a => cell i a = b)).card : ℝ) :=
      Finset.sum_le_sum hlower
    _ = (F.card : ℝ) := by exact_mod_cast (Finset.card_eq_sum_card_image (cell i) F).symm

/-- The recorded witness is an actual maximizing member of the finite family;
the original-point lower population is proved from regularity. -/
def MaximizingFiber (tubes : I → Finset (Finset α)) (cell : I → α → β)
    (threshold : I → ℕ) (i : I) (E F : Finset α) : Prop :=
  ∃ W ∈ tubes i, coverCount (cell i) E W = profile tubes cell i E ∧
    F = wholeCells (cell i) E W ∧ threshold i * profile tubes cell i E ≤ F.card

omit [Fintype α] in
lemma MaximizingFiber.image_card
    {tubes : I → Finset (Finset α)} {cell : I → α → β} {threshold : I → ℕ}
    {i : I} {E F : Finset α} (h : MaximizingFiber tubes cell threshold i E F) :
    (F.image (cell i)).card = profile tubes cell i E := by
  obtain ⟨W, _, hmax, rfl, _⟩ := h
  rw [wholeCells_image]
  exact hmax

omit [Fintype α] in
lemma MaximizingFiber.full
    {tubes : I → Finset (Finset α)} {cell : I → α → β} {threshold : I → ℕ}
    {i : I} {E F : Finset α} (h : MaximizingFiber tubes cell threshold i E F)
    {a b : α} (ha : a ∈ F) (hb : b ∈ E) (heq : cell i b = cell i a) : b ∈ F := by
  obtain ⟨W, _, _, rfl, _⟩ := h
  exact wholeCells_full (cell i) E W ha hb heq

/-- The maximizing footprint and its whole-cell fiber are constructed here. -/
theorem exists_maximizing_fiber (tubes : I → Finset (Finset α)) (cell : I → α → β)
    (coverage : Covers tubes) (threshold : I → ℕ) (i : I) (E : Finset α)
    (hE : E.Nonempty)
    (hregular : Regular (gridCells cell) (fun j => threshold j.1) E) :
    ∃ F ⊆ E, F.Nonempty ∧ MaximizingFiber tubes cell threshold i E F := by
  obtain ⟨W, hW, hmax, hmeet⟩ := exists_maximizing_footprint tubes cell coverage i E hE
  refine ⟨wholeCells (cell i) E W, wholeCells_subset (cell i) E W,
    wholeCells_nonempty (cell i) E W hmeet, W, hW, hmax, rfl, ?_⟩
  rw [← hmax]
  exact wholeCells_card_ge cell threshold E W i hregular

/-- Keeping the selector equality inside the single-step rule makes it available
on the final, positive-mass epoch produced by the generic constructor. -/
def ConcreteRule (select : Finset α → I) (tubes : I → Finset (Finset α))
    (cell : I → α → β) (threshold : I → ℕ)
    (i : I) (A E F : Finset α) : Prop :=
  i = select A ∧ MaximizingFiber tubes cell threshold i E F

/-- Actual finite tube-footprint families give disjoint rich original-point
fibers without profile, maximizing-witness, or extraction certificates as inputs.
The power budget comes from the proved bound M_i(A)≤|A|. -/
theorem exists_large_finite_cover_epoch [Fintype β] [Fintype I]
    (tubes : I → Finset (Finset α)) (cell : I → α → β)
    (coverage : Covers tubes) (threshold : I → ℕ)
    (select : Finset α → I) (K : ℕ) (hK : 1 < K) (A : Finset α)
    (hbudget : penalty (gridCells cell) (fun j => threshold j.1) A < A.card) :
    ∃ e : Epoch α I,
      e.start ⊆ A ∧ e.index = select e.start ∧
      ValidEpoch (gridCells cell) (fun j => threshold j.1) K (profile tubes cell)
        (ConcreteRule select tubes cell threshold) e ∧
      (∀ F ∈ e.pieces, F.Nonempty) ∧ e.pieces.Pairwise Disjoint ∧
      (∀ F ∈ e.pieces, threshold e.index * profile tubes cell e.index e.start ≤ K * F.card) ∧
      support e.pieces ⊆ A ∧
      A.card ≤ (Fintype.card I * rank K A.card) * (support e.pieces).card +
        penalty (gridCells cell) (fun j => threshold j.1) A := by
  classical
  obtain ⟨e, hsub, hvalid, hnonempty, hdisjoint, hmass⟩ :=
    exists_large_disjoint_epoch (gridCells cell) (fun j => threshold j.1)
      K (rank K A.card) hK (profile tubes cell)
      (profile_mono tubes cell) (profile_empty tubes cell) select
      (fun E hE => profile_positive tubes cell coverage (select E) E hE)
      (ConcreteRule select tubes cell threshold)
      (by
        intro S _ E _ hregular hE _
        obtain ⟨F, hFE, hFn, hmax⟩ := exists_maximizing_fiber tubes cell coverage threshold
          (select S) E hE hregular
        exact ⟨F, hFE, hFn, rfl, hmax⟩)
      A (profile_lt_pow_rank hK tubes cell A) hbudget
  have hpieces : e.pieces ≠ [] := by
    intro hz
    simp only [hz, mass_nil, Nat.mul_zero, Nat.zero_add] at hmass
    omega
  have hselected : e.index = select e.start := by
    obtain ⟨F, hF⟩ := List.exists_mem_of_ne_nil e.pieces hpieces
    obtain ⟨E, _, _, _, _, hrule⟩ := hvalid.2 F hF
    exact hrule.1
  refine ⟨e, hsub, hselected, hvalid, hnonempty, hdisjoint, ?_, ?_, ?_⟩
  · intro F hF
    obtain ⟨E, _, _, _, hactive, _, W, _, _, _, hrich⟩ := hvalid.2 F hF
    calc
      threshold e.index * profile tubes cell e.index e.start ≤
          threshold e.index * (K * profile tubes cell e.index E) := Nat.mul_le_mul_left _ hactive
      _ = K * (threshold e.index * profile tubes cell e.index E) := by ring
      _ ≤ K * F.card := Nat.mul_le_mul_left K hrich
  · apply support_subset
    intro F hF
    obtain ⟨E, hES, _, hFE, _⟩ := hvalid.2 F hF
    exact hFE.trans (hES.trans hsub)
  · rwa [support_card e.pieces hdisjoint]

end OriginalFinitePoints

end FiniteCoverProfileEpochs
