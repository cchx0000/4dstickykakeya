import Theorems.Thm_StickyKakeya4_native_merged_point_offsets
import Theorems.Thm_StickyKakeya4_native_original_parent_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeConfiguredOffsetField
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeMergedPointOffsets

/-- One actual old offset per occupied physical cell of the fixed pre-third
family. The point offset is the independently named, shared pointOffset on
that same U; no later subset changes either choice. -/
def cellField {Omega V : Type*} [Zero V]
    (U : Finset Omega) (point : Omega → E4) (xi : Omega → V)
    (Delta : ℝ) (c : Index) : V :=
  pointOffset U (fun w => wzDyadicCellIndex Delta (point w)) xi c

theorem cellField_witness {Omega V : Type*} [Zero V]
    (U : Finset Omega) (point : Omega → E4) (xi : Omega → V)
    (Delta : ℝ) (c : Index)
    (hc : c∈U.image (fun w => wzDyadicCellIndex Delta (point w))) :
    ∃w∈U, wzDyadicCellIndex Delta (point w)=c ∧ cellField U point xi Delta c=xi w :=
  pointOffset_witness U (fun w => wzDyadicCellIndex Delta (point w)) xi c (by
    simpa only [Finset.mem_image] using hc)

/-- The two chosen values come from actual U-preimages in the same old
cell. Only the already constructed support reader and old-cell coherence
are used; a configured-cell field is not an input. -/
theorem field_error_of_old_coherence
    {Omega Cell V : Type*} [SeminormedAddCommGroup V]
    (U : Finset Omega) (point : Omega → E4) (oldCell : Omega → Cell)
    (xi : Omega → V) (Delta osc : ℝ)
    (hread : ∀v∈U, ∀w∈U,
      wzDyadicCellIndex Delta (point v)=wzDyadicCellIndex Delta (point w) →
        oldCell v=oldCell w)
    (hcoh : ∀v∈U, ∀w∈U, oldCell v=oldCell w → ‖xi v-xi w‖≤osc)
    (p : E4) (hp : p∈U.image point) :
    ‖pointOffset U point xi p-cellField U point xi Delta (wzDyadicCellIndex Delta p)‖≤osc := by
  obtain ⟨v,hv,hvp,hoff⟩:=pointOffset_witness U point xi p (by
    simpa only [Finset.mem_image] using hp)
  have hc : wzDyadicCellIndex Delta p∈U.image (fun w => wzDyadicCellIndex Delta (point w)) := by
    exact mem_image.mpr ⟨v,hv,congrArg (wzDyadicCellIndex Delta) hvp⟩
  obtain ⟨w,hw,hwc,hfield⟩:=cellField_witness U point xi Delta _ hc
  rw [hoff,hfield]
  apply hcoh v hv w hw
  apply hread v hv w hw
  exact (congrArg (wzDyadicCellIndex Delta) hvp).trans hwc.symm

/-- The fixed pre-third field and point offset are retained literally on
every later incidence restriction, including the unique third core. -/
theorem field_error_on_subset
    {Omega Cell V : Type*} [SeminormedAddCommGroup V]
    (U T : Finset Omega) (hTU : T⊆U) (point : Omega → E4)
    (oldCell : Omega → Cell) (xi : Omega → V) (Delta osc : ℝ)
    (hread : ∀v∈U, ∀w∈U,
      wzDyadicCellIndex Delta (point v)=wzDyadicCellIndex Delta (point w) →
        oldCell v=oldCell w)
    (hcoh : ∀v∈U, ∀w∈U, oldCell v=oldCell w → ‖xi v-xi w‖≤osc)
    (p : E4) (hp : p∈T.image point) :
    ‖pointOffset U point xi p-cellField U point xi Delta (wzDyadicCellIndex Delta p)‖≤osc :=
  field_error_of_old_coherence U point oldCell xi Delta osc hread hcoh p
    (image_subset_image hTU hp)

end NativeConfiguredOffsetField
