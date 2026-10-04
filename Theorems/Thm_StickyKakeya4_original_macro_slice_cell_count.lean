import Theorems.Thm_StickyKakeya4_original_weighted_macro_selection
import Theorems.Thm_StickyKakeya4_original_window_physical_cells
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section
namespace OriginalMacroSliceCellCount
open Classical Finset OriginalPhaseCellPopulation OriginalWGrainDrift OriginalWindowPhysicalCells
open NativeTangentGridCoarsening OriginalWeightedMacroSelection
open scoped BigOperators
variable {P : Type*}
/-- The literal grid image of original transverse grain coordinates. -/
def grainCells (E : Finset P) (q : ℝ) (height x : P → ℝ) (y : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) : Finset (ℤ × ℤ) :=
  planarCells E (grainCoordinate height x y F) q
private lemma grain_center_bound {q : ℝ} (hq : 0 < q) (v : ℝ × ℝ) (k : ℤ × ℤ)
    (hk : (⌊v.1/q⌋,⌊v.2/q⌋)=k) :
    ‖v-(q*((k.1:ℝ)+1/2),q*((k.2:ℝ)+1/2))‖ ≤ q/2 := by
  have h1 : ⌊(v.1-0)/q⌋=k.1 := by simpa using congrArg Prod.fst hk
  have h2 : ⌊(v.2-0)/q⌋=k.2 := by simpa using congrArg Prod.snd hk
  have hp1 := coarse_floor_interval hq h1
  have hp2 := coarse_floor_interval hq h2
  change max |v.1-q*((k.1:ℝ)+1/2)| |v.2-q*((k.2:ℝ)+1/2)| ≤ q/2
  apply max_le_iff.mpr
  constructor
  · exact abs_le.mpr ⟨by nlinarith only [hp1.1,hp1.2],by nlinarith only [hp1.1,hp1.2]⟩
  · exact abs_le.mpr ⟨by nlinarith only [hp2.1,hp2.2],by nlinarith only [hp2.1,hp2.2]⟩
/-- The original physical slice count is controlled by its ACTUAL grain-grid
 image and the tangent interval. No local point population is assumed. -/
theorem original_slice_physical_cells (E : Finset P) (height x : P → ℝ) (y : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (z : ℝ) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hheight : ∀ p ∈ E, height p=z) (hF : ‖F z‖ ≤ 1) (hx : ∀ p ∈ E, |x p| ≤ 1) :
    ((physicalCells E q height x y).card:ℝ) ≤ (192/q)*(grainCells E q height x y F).card := by
  let index : P → ℤ × (ℤ × ℤ) := fun p =>
    (⌊x p/q⌋,(⌊(grainCoordinate height x y F p).1/q⌋,⌊(grainCoordinate height x y F p).2/q⌋))
  have hfiber : ∀ k ∈ E.image index,
      (((E.filter (fun p => index p=k)).image (physicalCell q height x y)).card:ℝ) ≤ 48 := by
    intro k _hk
    have hh := same_x_window_physical_cells (E.filter (fun p => index p=k)) height x y F z 0
      (q*((k.2.1:ℝ)+1/2),q*((k.2.2:ℝ)+1/2)) k.1 hq hq
      (show 0 ≤ q/2 by positivity) (by norm_num : (0:ℝ)≤1)
      (fun p hp => hheight p (mem_filter.mp hp).1) hF
      (fun p hp => by simpa [index] using congrArg Prod.fst (mem_filter.mp hp).2)
      (fun p hp => grain_center_bound hq _ _ (congrArg Prod.snd (mem_filter.mp hp).2))
    have hc : (q/q+2)*((2*(q/2)+1*q)/q+2)^2=(48:ℝ) := by
      rw [show 2*(q/2)+1*q=2*q by ring,div_self hq.ne',mul_div_cancel_right₀ (2:ℝ) hq.ne']
      norm_num
    simpa only [physicalCells,hc] using hh
  have hphys := image_card_le_real_mul_of_fiber_images E (physicalCell q height x y) index 48 hfiber
  let X := scalarCells E x q
  have hX : (X.card:ℝ) ≤ 4/q := by
    have hh := scalar_interval_grid_card E x (c := -1) hq (by norm_num : (0:ℝ)≤2)
      (fun p hp => ⟨(abs_le.mp (hx p hp)).1,by linarith [(abs_le.mp (hx p hp)).2]⟩)
    have hbase : 1 ≤ 1/q := (le_div_iff₀ hq).mpr (by simpa using hq1)
    have heq : 2/q+2 ≤ 4/q := by
      have htwo : 2/q=2*(1/q) := by ring
      have hfour : 4/q=4*(1/q) := by ring
      rw [htwo,hfour]
      linarith only [hbase]
    exact hh.trans heq
  have hsub : E.image index ⊆ X ×ˢ grainCells E q height x y F := by
    intro k hk
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hk
    exact mem_product.mpr ⟨mem_image_of_mem _ hp,mem_image_of_mem _ hp⟩
  have hindex : ((E.image index).card:ℝ) ≤ (X.card:ℝ)*(grainCells E q height x y F).card := by
    have hh := card_le_card hsub
    rw [card_product] at hh
    exact_mod_cast hh
  calc
    _ ≤ 48*((E.image index).card:ℝ) := hphys
    _ ≤ 48*((X.card:ℝ)*(grainCells E q height x y F).card) := mul_le_mul_of_nonneg_left hindex (by norm_num)
    _ ≤ 48*((4/q)*(grainCells E q height x y F).card) := by gcongr
    _ = _ := by ring
/-- Exact weighted macro-cell denominator, bounded by the original
 grain-grid populations at their original heights. -/
theorem original_macro_denominator (E : Finset P) (height x : P → ℝ) (y : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hF : ∀ z ∈ E.image height, ‖F z‖ ≤ 1) (hx : ∀ p ∈ E, |x p| ≤ 1) :
    (∑ k ∈ E.image (physicalCell q height x y),
      ((localHeights E (physicalCell q height x y) height k).card:ℝ)) ≤
    (192/q)*∑ z ∈ E.image height,
      ((grainCells (E.filter (fun p => height p=z)) q height x y F).card:ℝ) := by
  have heq : (∑ k ∈ E.image (physicalCell q height x y),
      ((localHeights E (physicalCell q height x y) height k).card:ℝ))=
      ∑ z ∈ E.image height, (((physicalCells (E.filter (fun p => height p=z)) q height x y).card):ℝ) := by
    exact_mod_cast sum_local_heights_eq_height_cells E (physicalCell q height x y) height
  rw [heq,mul_sum]
  apply sum_le_sum
  intro z hz
  exact original_slice_physical_cells (E.filter (fun p => height p=z)) height x y F z hq hq1
    (fun _ hp => (mem_filter.mp hp).2) (hF z hz) (fun p hp => hx p (mem_filter.mp hp).1)
end OriginalMacroSliceCellCount
