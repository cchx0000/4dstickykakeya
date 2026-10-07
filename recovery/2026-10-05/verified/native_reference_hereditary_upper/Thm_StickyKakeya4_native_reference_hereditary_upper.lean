import Theorems.Thm_StickyKakeya4_native_hereditary_scale_upper
import Theorems.Thm_StickyKakeya4_native_all_two_scale_configuration

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeReferenceHereditaryUpper
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalParentDensityCore NativeJointUniformCoarseRelations
open NativeConditionedPairMenu NativeTwoScaleConfiguration NativeTwoAxisPowerInterpolation
open NativeTwoAxisConditionalTransfer NativeFixedCompactKakeyaExponent NativeFixedSizeScaleMenu
open NativeMiddleWindowBalance NativeAllTwoScaleConfiguration NativeHereditaryScaleUpper

/-- Deterministic strengthening of the actual master's public fields. The
master is not invoked again: its one R, E, schedule, and physical maps supply
the upper for every later literal subset. Only the public reference loss t
is consumed, and all cost budgets come from the returned raw transfer cost. -/
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
    ∀F ⊆ E,∀m f : ℕ,m ≤ f → f ≤ level → ∀p : Parent,
      (NativeFiniteKakeyaCounts.multiplicity
        (NativeFullCoarseShadow.fullSource h R a level f (parentEdges D a (2^m) F p))).toReal ≤
        D.thickness^(-(3*t))*
          ((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-extremalExponent) := by
  let w := min (boundaryWindow t) ((t/16)/1000)
  have hw : 0 < w := lt_min (boundaryWindow_pos ht) (by positivity)
  have hw8 : w ≤ 1/8 := (min_le_left _ _).trans (min_le_right _ _)
  have hwloss : w ≤ t/16000 := by
    have hh : w ≤ (t/16)/1000 := min_le_right _ _
    linarith
  have hs : schedule = windowSchedule w hw.le g level := by
    rw [hschedule]
    rfl
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have hF : 0 < factor d (g+1) L := by
    have hh : 0 < d+(g+1)+(g+1) := by omega
    dsimp [factor,NativeLocalPairUniformCore.retentionCost]
    positivity
  have hQ : 1 ≤ coreRadix original R L := by
    dsimp [coreRadix,NativeSourceSizeBounds.radix]
    exact (by norm_num : 1 ≤ (4:ℕ)).trans (Nat.le_max_left _ _)
  have hbudgets := reference_cost_budgets hd hd1 heta ht.le
    (factor d (g+1) L) (coreRadix original R L) hF hQ
    (show 2*(seed/8) ≤ t/4 by linarith) hcost
  have hE : E ⊆ incidences original := hcore.1.trans (filter_subset _ _)
  have hER : ∀z∈E,z.1∈R := fun z hz => (mem_filter.mp (hcore.1 hz)).2
  have hlarge := large_level_of_grid w hw g level hg hgrid hgl
  apply hereditary_three_loss h original hbackbone.1 hbackbone.2.2.1 R E hE hER
    level hbackbone.2.1 extremalExponent_nonneg extremalExponent_le_three ht hw hw8 hwloss
    g (coreRadix original R L) hg hgl hgrid hlarge hbudgets.1 hbudgets.2
  · simpa only [hs] using hconditioned
  · intro i j hij q hq
    have hm := hreference (windowSchedule w hw.le g level i).val
      (windowSchedule w hw.le g level j).val hij
      (Nat.le_of_lt_succ (windowSchedule w hw.le g level j).isLt)
    exact (scheduled_image_bounds h R E a level (windowSchedule w hw.le g level i).val
      (windowSchedule w hw.le g level j).val t hER hm q hq).2

end NativeReferenceHereditaryUpper
