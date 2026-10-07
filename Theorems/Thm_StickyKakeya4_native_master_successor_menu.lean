import Theorems.Thm_StickyKakeya4_native_successor_angular_count
import Theorems.Thm_StickyKakeya4_native_reference_hereditary_upper

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4200000

noncomputable section
namespace NativeMasterSuccessorMenu
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalParentDensityCore NativeJointUniformCoarseRelations
open NativeConditionedPairMenu NativeTwoScaleConfiguration NativeFixedCompactKakeyaExponent
open NativeFixedSizeScaleMenu NativeMiddleWindowBalance NativeAllTwoScaleConfiguration
open NativeSuccessorAngularCount

/-- Actual successor angular menus from the one constructed master witness.
The grain count J is chosen independently before t; this theorem then works
at every adaptive pair of original dyadic depths. It neither chooses E again
nor assumes pointwise uniformity at a grain query scale. Spatial labels refer
to original delta/2-cell centers and remain separate from coarser point counts. -/
theorem from_master_reference {n d g L level : ℕ} {D : FiniteScaleSource n}
    {eta zeta a seed t : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E : Finset (Fin n × Index))
    (schedule : Fin (g+1) → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (ht : 0 < t) (heta : 0 ≤ eta) (hseed : seed ≤ t/16384)
    (hg : 0 < g) (hgl : g ≤ level)
    (hgrid : 1/(g:ℝ) < min (boundaryWindow t) ((t/16)/1000)/4)
    (hbackbone : HasOriginalBackbone D original R a level zeta)
    (hschedule : schedule = fullSchedule t ht g level)
    (hcore : IsCore D original R a eta zeta d (g+1) L Rel
      (fun j => 2^(schedule j).val) E)
    (hcost : (125*175616*16384:ℝ)*(factor d (g+1) L:ℝ)*(coreRadix original R L:ℝ)^2*
      D.thickness^(-eta) ≤ D.thickness^(-(seed/8)))
    (hconditioned : ∀i j,HasUniformFibers E (coreRadix original R L)
        (conditionedGlobalPair h R a level (schedule i).val (schedule j).val) ∧
      HasUniformFibers E (coreRadix original R L)
        (conditionedGlobalPoint h R a level (schedule i).val (schedule j).val))
    (hreference : ∀m f : ℕ,m ≤ f → f ≤ level → HasConditionalTwoScale h R E a level m f t) :
    ∀m f : ℕ,m ≤ f → f ≤ level → ∀q : Index,∀u : Fin 3 → ℤ,
      ((successorLabels D E m f q u).card:ℝ) ≤
        (131^3*2401:ℝ)*D.thickness^(-(3*t))*
          ((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-extremalExponent) := by
  have H := NativeReferenceHereditaryUpper.from_master_reference h original R E schedule Rel
    ht heta hseed hg hgl hgrid hbackbone hschedule hcore hcost hconditioned hreference
  have hE : E⊆incidences original := hcore.1.trans (filter_subset _ _)
  have hER : ∀z∈E,z.1∈R := fun z hz => (mem_filter.mp (hcore.1 hz)).2
  intro m f hmf hfl q u
  exact actual_successor_card h original hbackbone.1 hbackbone.2.2.1 R E hE hER
    level hbackbone.2.1 H m f hmf hfl q u

end NativeMasterSuccessorMenu
