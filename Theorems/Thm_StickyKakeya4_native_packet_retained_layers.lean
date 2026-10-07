import Theorems.Thm_StickyKakeya4_native_weighted_packet_layers

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

noncomputable section
namespace NativePacketRetainedLayers
open Classical Finset WeightedRichDirectionalLayers RichDirectionalLayers NativeWeightedPacketLayers
open scoped BigOperators
variable {α β : Type*}

/-- The reference lower weight is computed from the actual active packets. -/
def referenceMinimum (A E : Finset α) (packet : β → Finset α) (label : α → β) (w : α → ℕ) : ℕ :=
  if hE : E.Nonempty then
    (E.image (fun a => packetMass A packet w (label a))).min' (hE.image _)
  else 0

lemma referenceMinimum_le (A E : Finset α) (packet : β → Finset α) (label : α → β)
    (w : α → ℕ) (a : α) (ha : a∈E) :
    referenceMinimum A E packet label w ≤ packetMass A packet w (label a) := by
  have hE : E.Nonempty := ⟨a,ha⟩
  simp only [referenceMinimum,dif_pos hE]
  exact min'_le _ _ (mem_image_of_mem _ ha)

lemma le_referenceMinimum (A E : Finset α) (packet : β → Finset α) (label : α → β)
    (w : α → ℕ) (b : ℕ) (hE : E.Nonempty)
    (H : ∀a∈E,b ≤ packetMass A packet w (label a)) :
    b ≤ referenceMinimum A E packet label w := by
  simp only [referenceMinimum,dif_pos hE]
  apply le_min'
  intro z hz
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
  exact H a ha

/-- A single effective reference budget includes every ACTUAL overlap.
A geometric caller may bound it, but the construction never drops it. -/
def referenceBudget (A E : Finset α) (packet : ℕ → β → Finset α)
    (label : ℕ → α → β) (w : α → ℕ) (n : ℕ) : ℕ :=
  max 1 ((range n).sup (fun i => overlapCount A (E.image (label i)) (packet i))*mass A w)

lemma referenceBudget_positive (A E : Finset α) (packet : ℕ → β → Finset α)
    (label : ℕ → α → β) (w : α → ℕ) (n : ℕ) : 0 < referenceBudget A E packet label w n := by
  exact Nat.zero_lt_one.trans_le (le_max_left _ _)

lemma active_count_reference_budget (A E : Finset α) (packet : ℕ → β → Finset α)
    (label : ℕ → α → β) (w : α → ℕ) (n i : ℕ) (hi : i<n) :
    (E.image (label i)).card*referenceMinimum A E (packet i) (label i) w ≤
      referenceBudget A E packet label w n := by
  have hc := active_packet_count A E (packet i) (label i) w
    (referenceMinimum A E (packet i) (label i) w) (by
      intro c hc
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hc
      exact referenceMinimum_le A E (packet i) (label i) w a ha)
  have ho : overlapCount A (E.image (label i)) (packet i) ≤
      (range n).sup (fun j => overlapCount A (E.image (label j)) (packet j)) := le_sup (f := fun j => overlapCount A (E.image (label j)) (packet j)) (mem_range.mpr hi)
  exact (hc.trans (Nat.mul_le_mul_right (mass A w) ho)).trans (le_max_right _ _)

/-- Construct rich predecessor layers inside the actual retained source.
Their reference weights, overlap budget and thresholds are computed. Every
later point has predecessors in the preceding layer, with one total half-loss. -/
theorem construct_actual_packet_layers (A E : Finset α) (hEA : E⊆A)
    (packet : ℕ → β → Finset α) (label : ℕ → α → β) (w : α → ℕ) (n : ℕ)
    (hW : 0 < mass E w) (hcover : ∀i<n,∀a∈E,a∈packet i (label i a)) :
    let W := referenceBudget A E packet label w n
    let b := fun i => referenceMinimum A E (packet i) (label i) w
    let k := fun i => richThreshold (mass E w) W n (b i)
    let Omega := layers E packet label w k
    Omega 0=E ∧ (∀i,Omega (i+1)⊆Omega i) ∧
      (∀i,Omega i⊆A) ∧ mass E w ≤ 2*mass (Omega n) w ∧ 0 < mass (Omega n) w ∧
      (∀i<n,∀a∈Omega (i+1),k i ≤ packetMass (Omega i) (packet i) w (label i a)) ∧
      0 < ∏i∈range n,k i := by
  dsimp only
  let W := referenceBudget A E packet label w n
  let b := fun i => referenceMinimum A E (packet i) (label i) w
  let k := fun i => richThreshold (mass E w) W n (b i)
  have hb := richThreshold_budget (mass E w) W n (fun i => (E.image (label i)).card) b
    (referenceBudget_positive A E packet label w n) (fun i hi => active_count_reference_budget A E packet label w n i hi)
  change 2*(∑ i∈range n,(E.image (label i)).card*(k i-1)) ≤ mass E w at hb
  have hl := layers_mass_loss E packet label w k n hcover
  have hh : mass E w ≤ 2*mass (layers E packet label w k n) w := by omega
  refine ⟨rfl,layers_step_subset E packet label w k,?_,hh,?_,?_,?_⟩
  · intro i
    exact (layers_subset_start E packet label w k i).trans hEA
  · change 0 < mass (layers E packet label w k n) w
    omega
  · intro i _hi a ha
    exact layers_predecessors E packet label w k i a ha
  · exact richThreshold_product_positive (mass E w) W n b

end NativePacketRetainedLayers
