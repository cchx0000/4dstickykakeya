import Theorems.Thm_StickyKakeya4_native_dense_original_parent
import Theorems.Thm_StickyKakeya4_original_phase_cell_population
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalWeightedMacroSelection
open Classical Finset
open scoped BigOperators
variable {P Q H : Type*} [DecidableEq Q] [DecidableEq H]
/-- Every local carrier is a literal subset of the same original point set. -/
def localPoints (E : Finset P) (cell : P → Q) (q : Q) : Finset P := E.filter (fun p => cell p=q)
def localHeights (E : Finset P) (cell : P → Q) (height : P → H) (q : Q) : Finset H :=
  (localPoints E cell q).image height
lemma sum_original_local_points (E : Finset P) (cell : P → Q) :
    ∑ q ∈ E.image cell, ((localPoints E cell q).card:ℝ)=(E.card:ℝ) := by
  have hh := (Finset.card_eq_sum_card_image cell E).symm
  exact_mod_cast hh
/-- The actual occupied macro-cell/height incidence set. -/
def occupiedHeightPairs (E : Finset P) (cell : P → Q) (height : P → H) : Finset (Q × H) :=
  E.image (fun p => (cell p,height p))
lemma local_heights_pair_fiber (E : Finset P) (cell : P → Q) (height : P → H) (q : Q) :
    (localHeights E cell height q).card=
      ((occupiedHeightPairs E cell height).filter (fun v => v.1=q)).card := by
  apply card_bij (fun z _hz => (q,z))
  · intro z hz
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hz
    obtain ⟨hpE,hpq⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_image.mpr ⟨p,hpE,Prod.ext hpq rfl⟩,rfl⟩
  · intro z _hz w _hw he
    exact congrArg Prod.snd he
  · intro v hv
    obtain ⟨hvE,hvq⟩ := mem_filter.mp hv
    obtain ⟨p,hp,hpv⟩ := mem_image.mp hvE
    have hpq : cell p=q := (congrArg Prod.fst hpv).trans hvq
    refine ⟨v.2,mem_image.mpr ⟨p,mem_filter.mpr ⟨hp,hpq⟩,congrArg Prod.snd hpv⟩,?_⟩
    exact Prod.ext hvq.symm rfl
/-- Exact double counting of the denominator used in macro-cell selection. -/
theorem sum_local_heights_eq_pairs (E : Finset P) (cell : P → Q) (height : P → H) :
    ∑ q ∈ E.image cell, (localHeights E cell height q).card=(occupiedHeightPairs E cell height).card := by
  have hf : (occupiedHeightPairs E cell height).image Prod.fst=E.image cell := by
    simp only [occupiedHeightPairs,image_image]
    rfl
  calc
    _ = ∑ q ∈ E.image cell, ((occupiedHeightPairs E cell height).filter (fun v => v.1=q)).card :=
      sum_congr rfl (fun q _hq => local_heights_pair_fiber E cell height q)
    _ = _ := by rw [←hf]; exact (card_eq_sum_card_image Prod.fst _).symm
/-- Count the same occupied pairs by actual height instead of macro-cell. -/
theorem sum_local_heights_eq_height_cells (E : Finset P) (cell : P → Q) (height : P → H) :
    ∑ q ∈ E.image cell, (localHeights E cell height q).card=
      ∑ z ∈ E.image height, ((E.filter (fun p => height p=z)).image cell).card := by
  change _=∑ z ∈ E.image height, (localHeights E height cell z).card
  rw [sum_local_heights_eq_pairs,sum_local_heights_eq_pairs]
  have hs : (occupiedHeightPairs E cell height).image Prod.swap=occupiedHeightPairs E height cell := by
    simp only [occupiedHeightPairs,image_image]
    rfl
  rw [←hs,card_image_of_injective _ Prod.swap_injective]
/-- A source bound on occupied physical cells in each original height slice
 controls the exact weighted denominator; no local population lower is input. -/
theorem weighted_denominator_of_height_cells (E : Finset P) (cell : P → Q) (height : P → H)
    {K : ℝ} (hcap : ∀ z ∈ E.image height,
      (((E.filter (fun p => height p=z)).image cell).card:ℝ) ≤ K) :
    (∑ q ∈ E.image cell, ((localHeights E cell height q).card:ℝ)) ≤ K*(E.image height).card := by
  have heq : (∑ q ∈ E.image cell, ((localHeights E cell height q).card:ℝ))=
      ∑ z ∈ E.image height, ((((E.filter (fun p => height p=z)).image cell).card):ℝ) := by
    exact_mod_cast sum_local_heights_eq_height_cells E cell height
  rw [heq]
  calc
    _ ≤ ∑ _z ∈ E.image height, K := sum_le_sum hcap
    _ = _ := by simp [mul_comm]
/-- A genuine weighted macro-cell choice. The denominator is computed from
 the original height fibers; no local-density conclusion is a premise. -/
theorem exists_original_weighted_macro (E : Finset P) (cell : P → Q) (height : P → H)
    (hE : E.Nonempty) :
    ∃ q ∈ E.image cell, (localPoints E cell q).Nonempty ∧
      (E.card:ℝ) ≤ 2*((E.image cell).card:ℝ)*(localPoints E cell q).card ∧
      (E.card:ℝ)*(localHeights E cell height q).card ≤
        2*(∑ r ∈ E.image cell, ((localHeights E cell height r).card:ℝ))*(localPoints E cell q).card := by
  have hmass : 0 < ∑ q ∈ E.image cell, ((localPoints E cell q).card:ℝ) := by
    rw [sum_original_local_points]
    exact Nat.cast_pos.mpr hE.card_pos
  have hweight : 0 < ∑ q ∈ E.image cell, ((localHeights E cell height q).card:ℝ) := by
    apply Finset.sum_pos'
    · intro q _hq
      exact Nat.cast_nonneg _
    · obtain ⟨p,hp⟩ := hE
      refine ⟨cell p,mem_image_of_mem _ hp,?_⟩
      apply Nat.cast_pos.mpr
      apply Nonempty.card_pos
      exact ⟨height p,mem_image_of_mem height (mem_filter.mpr ⟨hp,rfl⟩)⟩
  obtain ⟨q,hq,hqp,hm,hd⟩ := NativeDenseOriginalParent.exists_mass_and_density (E.image cell)
    (fun q => ((localPoints E cell q).card:ℝ)) (fun q => ((localHeights E cell height q).card:ℝ))
    (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _) hmass hweight
  rw [sum_original_local_points] at hm hd
  exact ⟨q,hq,card_pos.mp (Nat.cast_pos.mp hqp),hm,hd⟩
/-- The same selection is made on the literal physical cube labels used
 by Definition 17.2(4), preserving the actual height and point identities. -/
theorem exists_physical_weighted_macro (E : Finset P) (height x : P → ℝ) (y : P → ℝ × ℝ)
    (scale : ℝ) (hE : E.Nonempty) :
    let cell := OriginalPhaseCellPopulation.physicalCell scale height x y
    ∃ q ∈ E.image cell, (localPoints E cell q).Nonempty ∧
      (E.card:ℝ) ≤ 2*((E.image cell).card:ℝ)*(localPoints E cell q).card ∧
      (E.card:ℝ)*(localHeights E cell height q).card ≤
        2*(∑ r ∈ E.image cell, ((localHeights E cell height r).card:ℝ))*(localPoints E cell q).card :=
  exists_original_weighted_macro E _ height hE
end OriginalWeightedMacroSelection
