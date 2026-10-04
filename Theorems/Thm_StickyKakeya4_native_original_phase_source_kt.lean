import Theorems.Thm_StickyKakeya4_native_original_phase_source_costs
import Theorems.Thm_StickyKakeya4_native_scheduled_scale_selection
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeOriginalPhaseSourceKT
open Classical NativeScheduledScaleSelection NativeOriginalPhaseSourceCosts NativeOriginalWindowKT
open OriginalPhaseCellPopulation OriginalPhaseGridPopulation OriginalPhaseWindowGraph
open OriginalWCoreDynamics OriginalWWitnessCounts OriginalWCoarseEscapeMenus NativeOriginalPhaseWindowGraph OriginalWGrainDrift
open FinitePlaneProjectionGrid
/-- Literal Definition17.2(4) field witnesses on occupied ORIGINAL physical
 cells at one allowed scale. The witness is a single vector for the cell. -/
def OriginalXiLaw {P : Type*} (E : Finset P) (height x : P → ℝ) (y xi : P → ℝ × ℝ)
    (Delta C0 : ℝ) : Prop :=
  ∀ q ∈ physicalCells E Delta height x y, ∃ center : ℝ × ℝ, ‖center‖ ≤ 1 ∧
    ∀ p ∈ E, physicalCell Delta height x y p=q → ‖xi p-center‖ ≤ C0*Delta
/-- Only the actual original scheduled scales are required. -/
def ScheduledOriginalXiLaw {P : Type*} (E : Finset P) (height x : P → ℝ) (y xi : P → ℝ × ℝ)
    (delta eta C0 : ℝ) : Prop :=
  ∀ n : ℕ, delta ≤ scheduledScale delta eta n → scheduledScale delta eta n ≤ 1 →
    OriginalXiLaw E height x y xi (scheduledScale delta eta n) C0
/-- Choose the actual single source vectors. This converts the literal
 per-occupied-cell existence into a field without discarding any label. -/
theorem exists_original_field {P : Type*} (E : Finset P) (height x : P → ℝ) (y xi : P → ℝ × ℝ)
    {Delta C0 : ℝ} (hSource : OriginalXiLaw E height x y xi Delta C0) :
    ∃ field : (ℤ × (ℤ × (ℤ × ℤ))) → ℝ × ℝ,
      (∀ p ∈ E, ‖xi p-field (physicalCell Delta height x y p)‖ ≤ C0*Delta) ∧
      ∀ q ∈ physicalCells E Delta height x y, ‖field q‖ ≤ 1 := by
  let field := fun q => if hq : q ∈ physicalCells E Delta height x y then
    Classical.choose (hSource q hq) else 0
  refine ⟨field,?_,?_⟩
  · intro p hp
    have hq : physicalCell Delta height x y p ∈ physicalCells E Delta height x y := Finset.mem_image_of_mem _ hp
    simpa only [field,dif_pos hq] using (Classical.choose_spec (hSource _ hq)).2 p hp rfl
  · intro q hq
    simpa only [field,dif_pos hq] using (Classical.choose_spec (hSource q hq)).1
/-- Select the original scheduled xi scale above the actual tangent grid.
 Its overshoot and the source field witnesses are outputs, not new inputs. -/
theorem exists_scheduled_original_field {P : Type*} (E : Finset P) (height x : P → ℝ) (y xi : P → ℝ × ℝ)
    {delta eta r C0 : ℝ} (hd : 0 < delta) (hd1 : delta < 1) (heta : 0 < eta)
    (hdr : delta ≤ r) (hr1 : r ≤ 1)
    (hSource : ScheduledOriginalXiLaw E height x y xi delta eta C0) :
    ∃ n : ℕ, delta ≤ scheduledScale delta eta n ∧ scheduledScale delta eta n ≤ 1 ∧
      r ≤ scheduledScale delta eta n ∧ scheduledScale delta eta n ≤ delta^(-eta)*r ∧
      ∃ field : (ℤ × (ℤ × (ℤ × ℤ))) → ℝ × ℝ,
        (∀ p ∈ E, ‖xi p-field (physicalCell (scheduledScale delta eta n) height x y p)‖ ≤ C0*scheduledScale delta eta n) ∧
        ∀ q ∈ physicalCells E (scheduledScale delta eta n) height x y, ‖field q‖ ≤ 1 := by
  obtain ⟨n,hdn,hn1,hrn,hnover⟩ := exists_scheduled_scale_above hd hd1 heta hdr hr1
  obtain ⟨field,hfield,hbox⟩ := exists_original_field E height x y xi (hSource n hdn hn1)
  exact ⟨n,hdn,hn1,hrn,hnover,field,hfield,hbox⟩
/-- The actual W-window A receives its absolute KT1 bound delta^(-9eta)
 directly from the ORIGINAL scheduled xi law, matrix entries, and physical
 window width. No A-regularity or final KT bound is an input. -/
theorem actual_window_source_power_KT {P T : Type*} [DecidableEq P] [DecidableEq T]
    (E : Finset P) (I : Finset (P × T)) (height x : P → ℝ) (y offset : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (hOriginal : TwoTubePathCollisionCount.points I ⊆ E)
    (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height)
    (z x0 : ℝ) (xi0 : ℝ × ℝ) (k : GrainLabel)
    {delta eta C0 r tau width sourceMesh mesh : ℝ}
    (hd : 0 < delta) (hd1 : delta < 1) (heta : 0 < eta) (hdr : delta ≤ r) (hr1 : r ≤ 1)
    (hC0 : 1 ≤ C0) (hC0cap : C0 ≤ delta^(-eta)) (hSmall : 5101248 ≤ delta^(-eta))
    (hSource : ScheduledOriginalXiLaw E height x y offset delta eta C0)
    (htau : r ≤ tau) (hwidth : 0 < width) (hwidthCap : width ≤ 40*C0*delta^(-eta)*r)
    (hFentries : |(F z 1).1| ≤ 1 ∧ |(F z 1).2| ≤ 1)
    (hSourceMesh : 0 < sourceMesh) (hmesh : 0 < mesh) (hmeshScale : mesh ≤ sourceMesh) :
    let Q := expanded (heightSlice S z)
      (fun s => grainCell width (grainCoordinate height x y F (rep I height S hSV s)))
      (fun s => phaseLabel r tau x0 xi0 x offset (rep I height S hSV s)) k
    ∀ i ∈ Q, ∀ R : ℝ, mesh ≤ R →
      ((Q.filter (fun j => dist3 (gridPoint sourceMesh i) (gridPoint sourceMesh j) ≤ R)).card:ℝ) ≤
        delta^(-9*eta)*R/mesh := by
  obtain ⟨n,_hdn,_hn1,hrDelta,hDelta,field,hfield,_hfieldbox⟩ :=
    exists_scheduled_original_field E height x y offset hd hd1 heta hdr hr1 hSource
  have hr : 0 < r := hd.trans_le hdr
  have hDelta0 : 0 < scheduledScale delta eta n := hr.trans_le hrDelta
  have hC00 : 0 ≤ C0 := by linarith only [hC0]
  have hfieldI : ∀ p ∈ TwoTubePathCollisionCount.points I,
      ‖offset p-field (physicalCell (scheduledScale delta eta n) height x y p)‖ ≤ C0*scheduledScale delta eta n :=
    fun p hp => hfield p (hOriginal hp)
  have hKT := actual_window_projection_KT I height x y offset F field S hSV z x0 xi0 k
    hr (hr.trans_le htau) hDelta0 hwidth (by norm_num : (0:ℝ)≤1) hC00
    (scalar_matrix_operator_bound (F z) hFentries) hfieldI hSourceMesh hmesh hmeshScale
  have hCost := source_window_KT_power hd hSmall hC0 hC0cap hr htau hrDelta hDelta hwidth.le hwidthCap
    (by norm_num : (0:ℝ)≤1) (le_refl (1:ℝ)) hC00 (le_refl C0)
  dsimp only
  intro i hi R hR
  exact (hKT i hi R hR).trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCost (hmesh.le.trans hR)) hmesh.le)
end NativeOriginalPhaseSourceKT
