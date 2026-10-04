import Theorems.Thm_StickyKakeya4_finite_phase_field_images
import Theorems.Thm_StickyKakeya4_original_w_grain_drift

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalPhaseCellPopulation
open Classical FinitePhaseFieldImages OriginalWGrainDrift

variable {P : Type*}

/-- Literal original physical cube label, with height first. All four
 coordinates are actual original coordinates, not phase coordinates. -/
def physicalCell (Delta : ℝ) (height x : P → ℝ) (y : P → ℝ × ℝ) (p : P) : ℤ × (ℤ × (ℤ × ℤ)) :=
  (⌊height p/Delta⌋,(⌊x p/Delta⌋,(⌊(y p).1/Delta⌋,⌊(y p).2/Delta⌋)))

def physicalCells (E : Finset P) (Delta : ℝ) (height x : P → ℝ) (y : P → ℝ × ℝ) :=
  E.image (physicalCell Delta height x y)

/-- Three coordinate interval counts bound the actual physical cube image at
 one exact original height. No point multiplicity or phase population is input. -/
theorem physical_cells_in_rectangle
    (E : Finset P) (height x : P → ℝ) (y : P → ℝ × ℝ) (z cX : ℝ) (cY : ℝ × ℝ)
    {Delta : ℝ} (hDelta : 0 < Delta) (hheight : ∀ p ∈ E, height p=z)
    (hx : ∀ p ∈ E, cX ≤ x p ∧ x p ≤ cX+Delta)
    (hy : ∀ p ∈ E,
      (cY.1 ≤ (y p).1 ∧ (y p).1 ≤ cY.1+Delta) ∧
      (cY.2 ≤ (y p).2 ∧ (y p).2 ≤ cY.2+Delta)) :
    ((physicalCells E Delta height x y).card : ℝ) ≤ 27 := by
  let X := NativeTangentGridCoarsening.scalarCells E x Delta
  let Y := NativeTangentGridCoarsening.planarCells E y Delta
  have hX : (X.card : ℝ) ≤ 3 := by
    have hc := NativeTangentGridCoarsening.scalar_interval_grid_card E x hDelta hDelta.le hx
    norm_num [hDelta.ne'] at hc
    exact_mod_cast hc
  have hY : (Y.card : ℝ) ≤ 9 := by
    have hc := NativeTangentGridCoarsening.planar_rectangle_grid_card E y hDelta hDelta.le hDelta.le hy
    norm_num [hDelta.ne'] at hc
    exact_mod_cast hc
  have hsub : physicalCells E Delta height x y ⊆ {⌊z/Delta⌋} ×ˢ (X ×ˢ Y) := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    refine Finset.mem_product.mpr ⟨?_,Finset.mem_product.mpr ⟨?_,?_⟩⟩
    · exact Finset.mem_singleton.mpr (congrArg (fun a : ℝ => ⌊a/Delta⌋) (hheight p hp))
    · exact Finset.mem_image_of_mem _ hp
    · exact Finset.mem_image_of_mem _ hp
  have hcard : ((physicalCells E Delta height x y).card : ℝ) ≤ (X.card : ℝ)*(Y.card : ℝ) := by
    have hn := Finset.card_le_card hsub
    simp only [Finset.card_product,Finset.card_singleton,one_mul] at hn
    exact_mod_cast hn
  calc
    _ ≤ (X.card : ℝ)*(Y.card : ℝ) := hcard
    _ ≤ 3*9 := mul_le_mul hX hY (by positivity) (by norm_num)
    _ = 27 := by norm_num

/-- A fixed tangent cell and a physical grain window fit inside a controlled
 number of ORIGINAL physical Delta-cubes. The y/xi distinction is preserved:
 this theorem uses y-F(z)x only and has no xi conclusion. -/
theorem same_x_and_grain_window_physical_cells
    (E : Finset P) (height x : P → ℝ) (y : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (z x₀ : ℝ) (g₀ : ℝ × ℝ) (k : ℤ)
    {r Delta W A : ℝ} (hr : 0 < r) (hDelta : 0 < Delta)
    (_hW : 0 ≤ W) (hA : 0 ≤ A) (hrDelta : r ≤ Delta) (hwidth : 2*W+A*r ≤ Delta)
    (hheight : ∀ p ∈ E, height p=z) (hF : ‖F z‖ ≤ A)
    (hcell : ∀ p ∈ E, ⌊(x p-x₀)/r⌋=k)
    (hgrain : ∀ p ∈ E, ‖grainCoordinate height x y F p-g₀‖ ≤ W) :
    ((physicalCells E Delta height x y).card : ℝ) ≤ 27 := by
  let c := x₀+r*(k:ℝ)
  let mid := c+r/2
  let center := g₀+F z mid
  let R := W+A*(r/2)
  have hx : ∀ p ∈ E, c ≤ x p ∧ x p ≤ c+r := by
    intro p hp
    have hh := NativeTangentGridCoarsening.coarse_floor_interval hr (hcell p hp)
    dsimp [c]
    constructor <;> linarith [hh.1,hh.2]
  have hmid : ∀ p ∈ E, |x p-mid| ≤ r/2 := by
    intro p hp
    dsimp [mid]
    exact abs_le.mpr ⟨by linarith [(hx p hp).1],by linarith [(hx p hp).2]⟩
  have hy : ∀ p ∈ E, ‖y p-center‖ ≤ R := by
    intro p hp
    calc
      _ = ‖(grainCoordinate height x y F p-g₀)+F z (x p-mid)‖ := by
        congr 1
        dsimp [grainCoordinate,center]
        rw [hheight p hp,map_sub]
        abel
      _ ≤ ‖grainCoordinate height x y F p-g₀‖+‖F z (x p-mid)‖ := norm_add_le _ _
      _ ≤ W+A*(r/2) := by
        apply add_le_add (hgrain p hp)
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul hF (hmid p hp) (norm_nonneg _) hA)
      _ = R := rfl
  apply physical_cells_in_rectangle E height x y z c (center.1-R,center.2-R) hDelta hheight
  · intro p hp
    exact ⟨(hx p hp).1,(hx p hp).2.trans (by linarith)⟩
  · intro p hp
    have hy₁ := abs_le.mp (max_le_iff.mp (hy p hp)).1
    have hy₂ := abs_le.mp (max_le_iff.mp (hy p hp)).2
    have hRwidth : 2*R ≤ Delta := by dsimp [R]; nlinarith
    simp only [Prod.fst_sub,Prod.snd_sub] at hy₁ hy₂
    change (center.1-R ≤ (y p).1 ∧ (y p).1 ≤ center.1-R+Delta) ∧
      (center.2-R ≤ (y p).2 ∧ (y p).2 ≤ center.2-R+Delta)
    exact ⟨⟨by linarith [hy₁.1],by linarith [hy₁.2]⟩,
      ⟨by linarith [hy₂.1],by linarith [hy₂.2]⟩⟩

/-- Bounded phase labels per actual tangent cell are DERIVED from the literal
 original field at physical scale Delta, after the physical cube count above.
 The ratio Delta/tau is retained; this is not inherited from macro consistency. -/
theorem original_phase_cells_over_x_cell
    (E : Finset P) (height x : P → ℝ) (y offset : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ)
    (field : (ℤ × (ℤ × (ℤ × ℤ))) → ℝ × ℝ)
    (z x₀ : ℝ) (g₀ xi₀ : ℝ × ℝ) (k : ℤ)
    {r tau Delta W A Cxi : ℝ} (hr : 0 < r) (htau : 0 < tau) (hDelta : 0 < Delta)
    (hW : 0 ≤ W) (hA : 0 ≤ A) (hCxi : 0 ≤ Cxi)
    (hrDelta : r ≤ Delta) (hwidth : 2*W+A*r ≤ Delta)
    (hheight : ∀ p ∈ E, height p=z) (hF : ‖F z‖ ≤ A)
    (hcell : ∀ p ∈ E, ⌊(x p-x₀)/r⌋=k)
    (hgrain : ∀ p ∈ E, ‖grainCoordinate height x y F p-g₀‖ ≤ W)
    (hfield : ∀ p ∈ E,
      ‖offset p-field (physicalCell Delta height x y p)‖ ≤ Cxi*Delta) :
    ((phaseCells E (fun p => ⌊(x p-x₀)/r⌋) tau xi₀ offset).card : ℝ) ≤
      27*(2*Cxi*Delta/tau+2)^2 := by
  rw [phase_card_of_fixed_tangent_cell E _ tau xi₀ offset k hcell]
  have hf := original_field_phase_image E (physicalCell Delta height x y) offset field xi₀
    htau hDelta.le hCxi hfield
  have hp := same_x_and_grain_window_physical_cells E height x y F z x₀ g₀ k hr hDelta
    hW hA hrDelta hwidth hheight hF hcell hgrain
  calc
    _ ≤ (2*Cxi*Delta/tau+2)^2*((E.image (physicalCell Delta height x y)).card : ℝ) := hf
    _ ≤ (2*Cxi*Delta/tau+2)^2*27 := mul_le_mul_of_nonneg_left hp (sq_nonneg _)
    _ = 27*(2*Cxi*Delta/tau+2)^2 := by ring

/-- Only an actual working-scale comparison Delta<=G*tau removes the large
 Delta/tau factor. Macro-only consistency remains quantitatively weaker. -/
theorem phase_cap_of_working_scale_ratio {N Cxi Delta tau G : ℝ}
    (htau : 0 < tau) (hDelta : 0 ≤ Delta) (hCxi : 0 ≤ Cxi) (hG : 0 ≤ G)
    (hgap : Delta ≤ G*tau) (hcap : N ≤ 27*(2*Cxi*Delta/tau+2)^2) :
    N ≤ 27*(2*Cxi*G+2)^2 := by
  have hm := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2*Cxi by positivity)
  have hr : 2*Cxi*Delta/tau ≤ 2*Cxi*G := (div_le_iff₀ htau).mpr (by nlinarith)
  have hl : 0 ≤ 2*Cxi*Delta/tau+2 := by positivity
  have hu : 0 ≤ 2*Cxi*G+2 := by positivity
  have hs : (2*Cxi*Delta/tau+2)^2 ≤ (2*Cxi*G+2)^2 := by nlinarith
  exact hcap.trans (mul_le_mul_of_nonneg_left hs (by norm_num))

end OriginalPhaseCellPopulation
