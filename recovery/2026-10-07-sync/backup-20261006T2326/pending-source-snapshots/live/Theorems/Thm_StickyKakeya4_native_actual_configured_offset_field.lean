import Theorems.Thm_StickyKakeya4_native_configured_offset_field
import Theorems.Thm_StickyKakeya4_native_actual_configured_point
import Theorems.Thm_StickyKakeya4_native_normalized_cell_relative_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
noncomputable section
namespace NativeActualConfiguredOffsetField
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeHorizontalGrainSlice CanonicalConfiguredE4Bridge NativeNormalizedCellRelativeMenu
open NativeMergedPointOffsets NativeConfiguredOffsetField

/-- The actual support constructor's wider-cell readback transports the
original source coherence to an explicitly constructed field. Both this
field and the merged point offset are chosen on U before the unique T.
The input old-cell coherence is the unchanged output of the native source
coherence constructor, not a configured-field assumption. -/
theorem from_actual_coherence {n : ℕ} {V : Type*} [SeminormedAddCommGroup V]
    (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (S U : Finset (Fin n × Index)) (hUS : U⊆S)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R0 M : ℕ) (hM : 0<M) (xi : Index → V)
    (hcoh : ∀z∈S, ∀w∈S,
      physicalCell D a (2^m) M p z.2=physicalCell D a (2^m) M p w.2 →
        ‖xi z.2-xi w.2‖≤(129/4:ℝ)*(64/(M:ℝ)))
    (hread : ∀z∈U, ∀w∈U,
      wzDyadicCellIndex ((64/(M:ℝ))/64)
        (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2)=
      wzDyadicCellIndex ((64/(M:ℝ))/64)
        (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 w.2) →
      physicalCell D a (2^m) M p z.2=physicalCell D a (2^m) M p w.2) :
    let point := fun z : Fin n × Index =>
      NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2
    let Delta := (64/(M:ℝ))/64
    0<Delta ∧ ∀T⊆U, ∀x∈T.image point,
      ‖pointOffset U point (fun z => xi z.2) x-
        cellField U point (fun z => xi z.2) Delta (wzDyadicCellIndex Delta x)‖≤2064*Delta := by
  intro point Delta
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  refine ⟨by dsimp [Delta]; positivity,?_⟩
  intro T hTU x hx
  have hh:=field_error_on_subset U T hTU point
    (fun z => physicalCell D a (2^m) M p z.2) (fun z => xi z.2)
    Delta ((129/4:ℝ)*(64/(M:ℝ))) hread
    (fun z hz w hw he => hcoh z (hUS hz) w (hUS hw) he) x hx
  exact hh.trans_eq (by dsimp [Delta]; ring)

end NativeActualConfiguredOffsetField
