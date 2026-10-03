import Theorems.Thm_StickyKakeya4_two_tube_path_collision_count
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

namespace GrainJumpArmCount
open TwoTubePathCollisionCount
open scoped BigOperators
variable {P T G : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq G]

/-- Original central point together with one of its actual incidence half-arms. -/
def halfArms (I : Finset (P × T)) : Finset (Σ _ : P, P × T) :=
  (points I).sigma (halfPaths I)

def armLabel (g : P → G) (h : Σ _ : P, P × T) : G := g h.1

/-- Two actual half-arms joined at equal original grain labels. The two central
points need not coincide; both original tube and outer-point labels remain. -/
def arms (I : Finset (P × T)) (g : P → G) := collisions (halfArms I) (armLabel g)

lemma mem_halfArms (I : Finset (P × T)) (h : Σ _ : P, P × T) :
    h ∈ halfArms I ↔ h.2 ∈ I ∧ (h.1, h.2.2) ∈ I := by
  constructor
  · intro hh
    obtain ⟨_, hh⟩ := Finset.mem_sigma.mp hh
    exact Finset.mem_filter.mp hh
  · rintro ⟨ho, hc⟩
    exact Finset.mem_sigma.mpr ⟨Finset.mem_image_of_mem Prod.fst hc,
      Finset.mem_filter.mpr ⟨ho, hc⟩⟩

lemma mem_arms (I : Finset (P × T)) (g : P → G)
    (h : (Σ _ : P, P × T) × (Σ _ : P, P × T)) :
    h ∈ arms I g ↔ h.1.2 ∈ I ∧ (h.1.1, h.1.2.2) ∈ I ∧
      h.2.2 ∈ I ∧ (h.2.1, h.2.2.2) ∈ I ∧ g h.1.1 = g h.2.1 := by
  simp only [arms, mem_collisions, mem_halfArms, armLabel, and_assoc]

lemma halfArms_card (I : Finset (P × T)) :
    (halfArms I).card = ∑ p ∈ points I, (halfPaths I p).card := by
  simp only [halfArms, Finset.card_sigma]

lemma arm_labels_subset (I : Finset (P × T)) (g : P → G) :
    (halfArms I).image (armLabel g) ⊆ (points I).image g := by
  intro u hu
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hu
  exact Finset.mem_image_of_mem g (Finset.mem_sigma.mp hh).1

omit [DecidableEq P] in
lemma grain_menu_mass_bound (A : Finset P) (g : P → G) (m : ℕ)
    (hgrain : ∀ u ∈ A.image g, m ≤ (A.filter (fun p => g p = u)).card) :
    (A.image g).card * m ≤ A.card := by
  calc
    (A.image g).card * m = ∑ u ∈ A.image g, m := by simp
    _ ≤ ∑ u ∈ A.image g, (A.filter (fun p => g p = u)).card :=
      Finset.sum_le_sum hgrain
    _ = A.card := (Finset.card_eq_sum_card_image g A).symm

/-- Exact grain-grouped one-arm identity used in WZ Lemma20.1. -/
theorem arms_card_eq_sum_grain_sq (I : Finset (P × T)) (g : P → G) :
    (arms I g).card = ∑ u ∈ (halfArms I).image (armLabel g),
      ((halfArms I).filter (fun h => g h.1 = u)).card ^ 2 := by
  exact card_collisions_eq_sum_fiber_sq (halfArms I) (armLabel g)

/-- The four-power count gains the actual lower grain population. There is no
per-tube degree lower bound or independent incidence assumption. -/
theorem grain_fourth_power_arm_bound (I : Finset (P × T)) (g : P → G) (m : ℕ)
    (hgrain : ∀ u ∈ (points I).image g,
      m ≤ ((points I).filter (fun p => g p = u)).card) :
    m * I.card ^ 4 ≤ (points I).card * (tubes I).card ^ 2 * (arms I g).card := by
  have ht : I.card ^ 2 ≤ (tubes I).card * (halfArms I).card := by
    rw [halfArms_card, card_incidence_eq_sum_tubeDegree, sum_halfPaths_eq_sum_tubeDegree_sq]
    exact nat_sum_sq_le_card_mul_sum_sq (tubes I) (tubeDegree I)
  have hc := square_card_le_image_mul_collisions (halfArms I) (armLabel g)
  have hm := grain_menu_mass_bound (points I) g m hgrain
  have hl := Finset.card_le_card (arm_labels_subset I g)
  have hp : m * (halfArms I).card ^ 2 ≤ (points I).card * (arms I g).card := by
    calc
      _ ≤ m * ((halfArms I).image (armLabel g)).card * (arms I g).card := by
        exact (Nat.mul_le_mul_left m hc).trans_eq (by dsimp [arms]; ring)
      _ ≤ m * ((points I).image g).card * (arms I g).card :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left m hl)
      _ ≤ (points I).card * (arms I g).card := by
        exact Nat.mul_le_mul_right _ (by simpa only [Nat.mul_comm] using hm)
  calc
    m * I.card ^ 4 = m * (I.card ^ 2) ^ 2 := by ring
    _ ≤ m * ((tubes I).card * (halfArms I).card) ^ 2 :=
      Nat.mul_le_mul_left m (Nat.pow_le_pow_left ht 2)
    _ = (tubes I).card ^ 2 * (m * (halfArms I).card ^ 2) := by ring
    _ ≤ (tubes I).card ^ 2 * ((points I).card * (arms I g).card) :=
      Nat.mul_le_mul_left _ hp
    _ = _ := by ring

/-- A second, actual finite label map pairs the retained one-arm objects.
Only its concrete menu size is caller-supplied; no original tuples are replaced. -/
theorem grain_eighth_power_collision_bound {L : Type*} [DecidableEq L]
    (I : Finset (P × T)) (g : P → G) (m N : ℕ)
    (label : ((Σ _ : P, P × T) × (Σ _ : P, P × T)) → L)
    (hgrain : ∀ u ∈ (points I).image g,
      m ≤ ((points I).filter (fun p => g p = u)).card)
    (hmenu : ((arms I g).image label).card ≤ N) :
    m ^ 2 * I.card ^ 8 ≤ (points I).card ^ 2 * (tubes I).card ^ 4 * N *
      (collisions (arms I g) label).card := by
  have h := grain_fourth_power_arm_bound I g m hgrain
  have hc := (square_card_le_image_mul_collisions (arms I g) label).trans
    (Nat.mul_le_mul_right _ hmenu)
  calc
    _ = (m * I.card ^ 4) ^ 2 := by ring
    _ ≤ ((points I).card * (tubes I).card ^ 2 * (arms I g).card) ^ 2 :=
      Nat.pow_le_pow_left h 2
    _ = ((points I).card ^ 2 * (tubes I).card ^ 4) * (arms I g).card ^ 2 := by ring
    _ ≤ ((points I).card ^ 2 * (tubes I).card ^ 4) *
        (N * (collisions (arms I g) label).card) := Nat.mul_le_mul_left _ hc
    _ = _ := by ring
end GrainJumpArmCount
