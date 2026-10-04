import Theorems.Thm_StickyKakeya4_original_literal_height_window
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
noncomputable section
namespace OriginalWholeMacroWindow
open Classical Finset OriginalLiteralHeightWindow OriginalWeightedMacroSelection
open OriginalMacroGrainReadback OriginalPhaseCellPopulation
variable {P : Type*}
/-- A physical macro-cell occupied after height-window selection is the
 ENTIRE same original macro-cell. Its original labels are not a new thinning. -/
theorem actual_macro_readback (E : Finset P) (height x : P → ℝ) (y : P → ℝ × ℝ)
    (q : ℝ) (j : ℤ) (k : ℤ × (ℤ × (ℤ × ℤ)))
    (hk : k ∈ (window E height q j).image (physicalCell q height x y)) :
    k.1=j ∧
      localPoints (window E height q j) (physicalCell q height x y) k=
        localPoints E (physicalCell q height x y) k ∧
      localHeights (window E height q j) (physicalCell q height x y) height k=
        localHeights E (physicalCell q height x y) height k := by
  obtain ⟨p0,hp0,hp0k⟩ := mem_image.mp hk
  have hkheight : k.1=j := (congrArg Prod.fst hp0k).symm.trans (mem_filter.mp hp0).2
  have heq : localPoints (window E height q j) (physicalCell q height x y) k=
      localPoints E (physicalCell q height x y) k := by
    ext p
    simp only [localPoints,window,mem_filter]
    constructor
    · rintro ⟨⟨hp,_⟩,hpk⟩
      exact ⟨hp,hpk⟩
    · rintro ⟨hp,hpk⟩
      exact ⟨⟨hp,(congrArg Prod.fst hpk).trans hkheight⟩,hpk⟩
  refine ⟨hkheight,heq,?_⟩
  unfold localHeights
  rw [heq]
/-- The literal original grain and tangent-fiber carriers are unchanged at
 every retained height, with full membership readback. -/
theorem actual_grain_fiber_readback (E : Finset P) (height : P → ℝ) (grain : P → ℝ × ℝ)
    (q : ℝ) (j : ℤ) (z : ℝ) (hz : z ∈ (window E height q j).image height) :
    z ∈ E.image height ∧
      grains (window E height q j) height grain z=grains E height grain z ∧
      ∀ g, tangentFiber (window E height q j) height grain z g=tangentFiber E height grain z g := by
  rw [actual_height_image] at hz
  obtain ⟨hzE,hzj⟩ := mem_filter.mp hz
  have hs := whole_height_fiber E height q j z hzj
  refine ⟨hzE,?_,?_⟩
  · unfold grains
    rw [hs]
  · intro g
    unfold tangentFiber
    rw [hs]
end OriginalWholeMacroWindow
