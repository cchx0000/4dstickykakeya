import Theorems.Thm_StickyKakeya4_weighted_rich_directional_layers

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeWeightedPacketLayers
open Classical Finset WeightedRichDirectionalLayers RichDirectionalLayers
open scoped BigOperators
variable {α β : Type*}

/-- Current ORIGINAL weight in the actual reference packet. Packets may overlap. -/
def packetMass (B : Finset α) (packet : β → Finset α) (w : α → ℕ) (c : β) : ℕ :=
  mass (B∩packet c) w

def restriction (B : Finset α) (packet : β → Finset α) (label : α → β)
    (w : α → ℕ) (k : ℕ) : Finset α :=
  B.filter (fun a => k ≤ packetMass B packet w (label a))

lemma restriction_subset (B : Finset α) (packet : β → Finset α) (label : α → β)
    (w : α → ℕ) (k : ℕ) : restriction B packet label w k ⊆ B := filter_subset _ _

lemma restriction_predecessors (B : Finset α) (packet : β → Finset α) (label : α → β)
    (w : α → ℕ) (k : ℕ) (a : α) (ha : a∈restriction B packet label w k) :
    k ≤ packetMass B packet w (label a) := (mem_filter.mp ha).2

/-- Deletion is charged only to the occupied labels, even though their
reference packets overlap. Every assigned source point really lies in its packet. -/
theorem restriction_mass_loss (A B : Finset α) (packet : β → Finset α) (label : α → β)
    (w : α → ℕ) (k : ℕ) (hBA : B⊆A) (hcover : ∀a∈A,a∈packet (label a)) :
    mass B w ≤ mass (restriction B packet label w k) w+(A.image label).card*(k-1) := by
  let D := B.filter (fun a => ¬k ≤ packetMass B packet w (label a))
  have hD : D⊆B := filter_subset _ _
  have hc : ∀c∈A.image label,mass (classFiber D label c) w ≤ k-1 := by
    intro c _hc
    by_cases hne : (classFiber D label c).Nonempty
    · obtain ⟨a,ha⟩ := hne
      obtain ⟨haD,hac⟩ := mem_filter.mp ha
      have hlo := (mem_filter.mp haD).2
      have hsub : classFiber D label c ⊆ B∩packet (label a) := by
        intro z hz
        obtain ⟨hzD,hzc⟩ := mem_filter.mp hz
        have hzp := hcover z (hBA (hD hzD))
        rw [hzc,hac.symm] at hzp
        exact mem_inter.mpr ⟨hD hzD,hzp⟩
      have hm := mass_mono _ _ w hsub
      change _ ≤ packetMass B packet w (label a) at hm
      omega
    · simp only [not_nonempty_iff_eq_empty.mp hne,mass,sum_empty]
      exact Nat.zero_le _
  have hl : mass D w ≤ (A.image label).card*(k-1) := by
    calc
      _ = ∑c∈A.image label,mass (classFiber D label c) w :=
        (sum_fiberwise_of_maps_to (fun a ha => mem_image_of_mem label (hBA (hD ha))) w).symm
      _ ≤ ∑_c∈A.image label,(k-1) := sum_le_sum hc
      _ = _ := by simp
  have hp := sum_filter_add_sum_filter_not B (fun a => k ≤ packetMass B packet w (label a)) w
  change mass (restriction B packet label w k) w+mass D w=mass B w at hp
  omega

/-- The largest ACTUAL number of retained packet labels covering an original
point. Geometry will bound this computed quantity by a fixed constant. -/
def overlapCount (A : Finset α) (C : Finset β) (packet : β → Finset α) : ℕ :=
  A.sup (fun a => (C.filter (fun c => a∈packet c)).card)

lemma cover_count_le_overlap (A : Finset α) (C : Finset β) (packet : β → Finset α)
    (a : α) (ha : a∈A) :
    (C.filter (fun c => a∈packet c)).card ≤ overlapCount A C packet :=
  by
    exact le_sup (f := fun x => (C.filter (fun c => x∈packet c)).card) ha

/-- Exact double counting uses the unchanged source weight, with no
normalization of individual packets. -/
theorem packet_mass_sum (A : Finset α) (C : Finset β) (packet : β → Finset α) (w : α → ℕ) :
    ∑c∈C,packetMass A packet w c =
      ∑a∈A,(C.filter (fun c => a∈packet c)).card*w a := by
  calc
    _ = ∑a∈A,∑c∈C,if a∈packet c then w a else 0 := by
      simp only [packetMass,mass,←filter_mem_eq_inter,sum_filter]
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro a _ha
      rw [←sum_filter]
      simp

theorem packet_mass_sum_le (A : Finset α) (C : Finset β) (packet : β → Finset α) (w : α → ℕ) :
    ∑c∈C,packetMass A packet w c ≤ overlapCount A C packet*mass A w := by
  rw [packet_mass_sum,mass,mul_sum]
  exact sum_le_sum (fun a ha => Nat.mul_le_mul_right (w a) (cover_count_le_overlap A C packet a ha))

theorem active_packet_count (A E : Finset α) (packet : β → Finset α) (label : α → β)
    (w : α → ℕ) (b : ℕ)
    (hlower : ∀c∈E.image label,b ≤ packetMass A packet w c) :
    (E.image label).card*b ≤ overlapCount A (E.image label) packet*mass A w := by
  calc
    _ = ∑_c∈E.image label,b := by simp
    _ ≤ ∑c∈E.image label,packetMass A packet w c := sum_le_sum hlower
    _ ≤ _ := packet_mass_sum_le A (E.image label) packet w

/-- Explicit repeated restriction on the same original source and weights. -/
def layers (E : Finset α) (packet : ℕ → β → Finset α) (label : ℕ → α → β)
    (w : α → ℕ) (k : ℕ → ℕ) : ℕ → Finset α
  | 0 => E
  | i+1 => restriction (layers E packet label w k i) (packet i) (label i) w (k i)

lemma layers_step_subset (E : Finset α) (packet : ℕ → β → Finset α) (label : ℕ → α → β)
    (w : α → ℕ) (k : ℕ → ℕ) (i : ℕ) :
    layers E packet label w k (i+1) ⊆ layers E packet label w k i := restriction_subset _ _ _ _ _

lemma layers_subset_start (E : Finset α) (packet : ℕ → β → Finset α) (label : ℕ → α → β)
    (w : α → ℕ) (k : ℕ → ℕ) (i : ℕ) : layers E packet label w k i ⊆ E := by
  induction i with
  | zero => exact Subset.refl _
  | succ i ih => exact (layers_step_subset E packet label w k i).trans ih

lemma layers_predecessors (E : Finset α) (packet : ℕ → β → Finset α) (label : ℕ → α → β)
    (w : α → ℕ) (k : ℕ → ℕ) (i : ℕ) (a : α)
    (ha : a∈layers E packet label w k (i+1)) :
    k i ≤ packetMass (layers E packet label w k i) (packet i) w (label i a) :=
  restriction_predecessors _ _ _ _ _ _ ha

theorem layers_mass_loss (E : Finset α) (packet : ℕ → β → Finset α) (label : ℕ → α → β)
    (w : α → ℕ) (k : ℕ → ℕ) (n : ℕ) (hcover : ∀i<n,∀a∈E,a∈packet i (label i a)) :
    mass E w ≤ mass (layers E packet label w k n) w+
      ∑i∈range n,(E.image (label i)).card*(k i-1) := by
  induction n with
  | zero => simp [layers]
  | succ n ih =>
    have hprev := ih (fun i hi => hcover i (by omega))
    have hstep := restriction_mass_loss E (layers E packet label w k n) (packet n) (label n) w (k n)
      (layers_subset_start E packet label w k n) (hcover n (by omega))
    rw [sum_range_succ]
    change mass E w ≤ mass (restriction (layers E packet label w k n) (packet n) (label n) w (k n)) w+_
    omega

end NativeWeightedPacketLayers
