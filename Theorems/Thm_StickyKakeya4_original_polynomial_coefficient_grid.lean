import Theorems.Thm_StickyKakeya4_finite_plane_projection_grid
import Theorems.Thm_StickyKakeya4_original_tensor_frostman

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical

namespace OriginalPolynomialCoefficientGrid
open FinitePlaneProjectionGrid

def grid (M : ℕ) : Finset ℝ := (slopes M).image (fun u => (1+u)/2)

lemma grid_card (M : ℕ) : (grid M).card=M+1 := by
  unfold grid
  rw [Finset.card_image_of_injective _ (by intro x y h; linarith),slopes_card]

lemma grid_bounds {M : ℕ} {v : ℝ} (hv : v∈grid M) : (1/2:ℝ) ≤ v ∧ v ≤ 1 := by
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
  have hu1 := slope_abs_le_one hu
  obtain ⟨k,_hk,hku⟩ := Finset.mem_image.mp hu
  have hu0 : 0 ≤ u := by rw [← hku]; exact mul_nonneg (mesh_pos M).le (Nat.cast_nonneg _)
  constructor <;> nlinarith only [hu0,le_abs_self u,hu1]

/-- The actual equally spaced coefficient grid has the interval probability
bound needed for tensor collision averaging. -/
theorem original_coefficient_interval_count (M : ℕ) (c : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (((grid M).filter (fun v => |v-c| ≤ r)).card:ℝ) ≤
      (4*r+2*mesh M)*(grid M).card := by
  have hsub : (grid M).filter (fun v => |v-c| ≤ r) ⊆
      ((slopes M).filter (fun u => |u-(2*c-1)| ≤ 2*r)).image (fun u => (1+u)/2) := by
    intro v hv
    obtain ⟨hv,hnear⟩ := Finset.mem_filter.mp hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    apply Finset.mem_image.mpr
    refine ⟨u,Finset.mem_filter.mpr ⟨hu,?_⟩,rfl⟩
    have he : u-(2*c-1)=2*((1+u)/2-c) := by ring
    rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith only [hnear]
  have hc : (((grid M).filter (fun v => |v-c| ≤ r)).card:ℝ) ≤
      ((slopes M).filter (fun u => |u-(2*c-1)| ≤ 2*r)).card := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
  have hb := slope_interval_count M (2*c-1) (show 0 ≤ 2*r by positivity)
  rw [grid_card,← slopes_card M]
  nlinarith only [hc,hb]

/-- The coefficient family is chosen concretely from the requested mesh. -/
lemma coefficient_mesh_choice {delta : ℝ} (hd : 0 < delta) :
    mesh ⌈1/delta⌉₊ ≤ delta := by
  have hc := Nat.le_ceil (1/delta)
  have hm := (div_le_iff₀ hd).mp hc
  unfold mesh
  apply (div_le_iff₀ (show 0 < (⌈1/delta⌉₊:ℝ)+1 by positivity)).mpr
  nlinarith only [hm,hd]

end OriginalPolynomialCoefficientGrid
