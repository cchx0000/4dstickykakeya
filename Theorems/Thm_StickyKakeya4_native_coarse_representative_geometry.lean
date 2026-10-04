import Theorems.Thm_StickyKakeya4_native_coarse_shading_capacity
import Theorems.Thm_StickyKakeya4_native_original_slope_cube_packing
import Theorems.Thm_StickyKakeya4_native_compact_chart_reach
import Theorems.Thm_StickyKakeya4_native_normalized_parent_carrier_metric
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
noncomputable section
namespace NativeCoarseRepresentativeGeometry
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalCellChartGeometry NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentPhysicalData
open NativeOriginalPaddedCells NativeCoarseShadingCapacity NativeUnitParentNormalization
open NativeContractedUnitParent NativeOriginalSlopeCubePacking NativeOriginalParentCount
open scoped BigOperators ENNReal RealInnerProductSpace

/-- Zero-parent padding leaves the ACTUAL original direction unchanged.
Only one common spatial contraction and height translation is used. -/
lemma direction_zero_parent {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (i : Fin n) :
    direction (NativeContractedUnitParent.line D a (0,0) i)=direction (D.line i) := by
  have hs : newSlope (D.line i) (0,0)=EuclideanAlignmentPatches.euclidean (slope (D.line i)) := by
    ext j
    simp only [newSlope,Pi.zero_apply,Int.cast_zero,sub_zero,EuclideanAlignmentPatches.euclidean]
  change (northSlopeDirection (newSlope (D.line i) (0,0)):E4)=_
  rw [hs]
  exact normalize_original_slope (D.line i) (h.1.2.2.2.2.1 i) (h.2.1.1 i)

lemma zero_parent_valid_slab {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (i : Fin n) :
    IsValidLine (NativeContractedUnitParent.line D a (0,0) i) ∧
      (1/2:ℝ) ≤ direction (NativeContractedUnitParent.line D a (0,0) i) (3:Fin 4) ∧
      ContainsWZHeightSlab (NativeContractedUnitParent.line D a (0,0) i)
        (Set.Icc (-(1/4:ℝ)) (1/4:ℝ)) := by
  have hv : IsValidLine (newLine (D.line i) (mesh D) (shift D a) (0,0)) :=
    NativeGraphMarkedLine.valid _ _ _
  have hc := h.2.1.1 i
  rw [←direction_zero_parent h a i] at hc
  have hz : wzMarkedCenterHeight (NativeContractedUnitParent.line D a (0,0) i)=0 := by
    rw [NativeContractedUnitParent.line,contractLine_center_height,newLine,NativeGraphMarkedLine.center_height,zero_div]
  refine ⟨contractLine_valid hv,hc,?_⟩
  have hh := containsWZHeightSlab_of_center_bin (NativeContractedUnitParent.line D a (0,0) i)
    (c:=(1/2:ℝ)) (u:=0) (h:=0) (by norm_num) hc (by rw [hz]) (by rw [hz]; simp)
  simpa only [add_zero,zero_sub,zero_add,show (1/2:ℝ)/2=1/4 by norm_num] using hh

/-- Any original shading height projects to the TRUE unit segment of any
original representative. The common original height window gives the buffer. -/
lemma projected_point_mem_front {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (i j : Fin n) (k : Index) (hk : k∈original i) :
    frontPoint D a (0,0) j k∈unitFront {NativeContractedUnitParent.line D a (0,0) j} := by
  have ht := (original_cell_bounds h original horiginal a ha ((mem_incidences original i k).mpr hk)).1
  change |oldTime D a k| ≤ 1 at ht
  let l := newLine (D.line j) (mesh D) (shift D a) (0,0)
  have hc : (1/2:ℝ) ≤ direction l (3:Fin 4) := by
    have hh := h.2.1.1 j
    rwa [←direction_zero_parent h a j] at hh
  have hcp : 0 < direction l (3:Fin 4) := by linarith
  have hu : |(oldTime D a k/4-0)/direction l (3:Fin 4)| ≤ 1/2 := by
    rw [sub_zero,abs_div,abs_of_pos hcp,abs_div]
    norm_num
    apply (div_le_iff₀ hcp).mpr
    linarith
  have hf := rawFrontParam_mem_unitFront_singleton l (abs_le.mp hu)
  dsimp only [l,newLine] at hf
  rw [NativeGraphMarkedLine.rawFrontParam_graph] at hf
  exact contract_front l (Set.mem_image_of_mem contractPoint hf)

lemma projected_rows_meet_front {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N B : ℕ) (hB : 0 < B) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (hE : ∀e∈E,e.2∈original e.1) (p : Parent) (q : Index)
    (hq : q∈rows D a N B rep E p) :
    ∃t : Set.Icc (-(1/2:ℝ)) (1/2:ℝ),
      rawFrontParam (NativeContractedUnitParent.line D a (0,0) (rep p),(t:ℝ))∈
        wzDyadicCell ((B:ℝ)*D.thickness/128) q := by
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hq
  obtain ⟨hv,hvp⟩ := mem_filter.mp hv
  obtain ⟨e,he,rfl⟩ := mem_image.mp hv
  change parentLabel D a N e.1=p at hvp
  have hf := projected_point_mem_front h original horiginal ha e.1 (rep p) e.2 (hE e he)
  obtain ⟨l,hl,t,ht,heq⟩ := hf
  have hl' : l=NativeContractedUnitParent.line D a (0,0) (rep p) := by simpa using hl
  subst l
  refine ⟨⟨t,ht⟩,?_⟩
  have hm : 0 < (B:ℝ)*D.thickness/128 := by have hd:=h.1.2.1; positivity
  have hh := mem_wzDyadicCell_index hm (frontPoint D a (0,0) (rep p) e.2)
  change rawFrontParam _∈wzDyadicCell _ (projectedLabel D a B (rep (parentLabel D a N e.1)) e.2)
  rw [hvp]
  simpa only [projectedLabel,heq,rawFrontParam] using hh

/-- Actual coarse shadings are made from front-meeting cubes at exactly half
the output tube thickness, so the original native comparability is preserved. -/
theorem projected_shading_subset_tube {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N B : ℕ) (hB : 0 < B) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (hE : ∀e∈E,e.2∈original e.1) (p : Parent) :
    wzCellShading ((B:ℝ)*D.thickness/128) (fun _ : Fin 1 => rows D a N B rep E p) 0 ⊆
      markedUnitTube (NativeContractedUnitParent.line D a (0,0) (rep p)) ((B:ℝ)*D.thickness/64) := by
  have hm : 0 < (B:ℝ)*D.thickness/128 := by have hd:=h.1.2.1; positivity
  have hh := wzDyadicCells_meeting_markedLine_subset_two_mul_tube
    (NativeContractedUnitParent.line D a (0,0) (rep p)) hm (rows D a N B rep E p)
    (projected_rows_meet_front h original horiginal ha N B hB rep E hE p)
  simpa only [wzCellShading,show 2*((B:ℝ)*D.thickness/128)=(B:ℝ)*D.thickness/64 by ring] using hh

lemma compact_mark_offset {l : MarkedLine} (hl : l∈fixedCompactClass) :
    |mark l| ≤ 2 ∧ ‖offset l‖ ≤ 2 := by
  change dist l 0 ≤ 2 at hl
  rw [dist_zero_right] at hl
  change max (max ‖direction l‖ ‖offset l‖) |mark l| ≤ 2 at hl
  exact ⟨(le_max_right _ _).trans hl,((le_max_right _ _).trans (le_max_left _ _)).trans hl⟩

lemma zero_intercept_bound {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀i,D.line i∈fixedCompactClass)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (i : Fin n) (j : Fin 3) :
    |newIntercept (D.line i) (mesh D) (shift D a) (0,0) j| ≤ 1/2 := by
  have hreach := NativeCompactChartReach.chartReach_le_of_marks h ha (by norm_num : (0:ℝ)≤2)
    (fun k => (compact_mark_offset (hK k)).1)
  have hr := (le_chartReach D a i).trans hreach
  have ho := (coordinate_abs_le_norm (offset (D.line i)) j.castSucc).trans (compact_mark_offset (hK i)).2
  have hs := slope_bound (D.line i) (h.1.2.2.2.2.1 i) (h.2.1.1 i) j
  have he : newIntercept (D.line i) (mesh D) (shift D a) (0,0) j=
      (offset (D.line i) j.castSucc+slope (D.line i) j*
        ((shift D a:ℝ)*mesh D-offset (D.line i) (3:Fin 4)))/16 := by
    simp only [newIntercept,shiftedIntercept,intercept,Pi.zero_apply,Int.cast_zero,sub_zero]
    ring
  rw [he,abs_div]
  norm_num
  have hm := mul_le_mul hs hr (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
  rw [←abs_mul] at hm
  have hh := (abs_add_le _ _).trans (add_le_add ho hm)
  linarith

/-- Coarse representatives stay in the SAME fixed K0. Compactness controls
marks and offsets before delta; no unrestricted extremizer is placed in K0. -/
theorem zero_parent_mem_fixedCompactClass {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀i,D.line i∈fixedCompactClass)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (i : Fin n) : NativeContractedUnitParent.line D a (0,0) i∈fixedCompactClass := by
  let u := newSlope (D.line i) (0,0)
  let v := newIntercept (D.line i) (mesh D) (shift D a) (0,0)
  let theta : E4 := northSlopeDirection u
  let x0 := ActualSlopeSource.heightPoint v 0
  have htheta : ‖theta‖=1 := (northSlopeDirection u).property
  have hv : ‖v‖ ≤ 1 := by
    have hh := NativeNormalizedParentCarrierMetric.euclidean_three_norm_le_two v (1/2) (by norm_num)
      (zero_intercept_bound h hK ha i)
    linarith
  have hx : ‖x0‖ ≤ 1 := by
    simpa only [x0,NativeNormalizedParentCarrierMetric.heightPoint_zero_norm] using hv
  have hm : |inner ℝ x0 theta| ≤ 1 := by
    have hh := abs_real_inner_le_norm x0 theta
    rw [htheta,mul_one] at hh
    exact hh.trans hx
  have ho : ‖x0-inner ℝ x0 theta • theta‖ ≤ 2 := by
    have hh := norm_sub_le x0 (inner ℝ x0 theta • theta)
    rw [norm_smul,Real.norm_eq_abs,htheta,mul_one] at hh
    linarith
  have hb : ‖newLine (D.line i) (mesh D) (shift D a) (0,0)‖ ≤ 2 := by
    change ‖NativeGraphMarkedLine.ofGraph u v 0‖ ≤ 2
    simp only [NativeGraphMarkedLine.ofGraph,zero_smul,add_zero,Prod.norm_def,Real.norm_eq_abs]
    change max (max ‖theta‖ ‖x0-inner ℝ x0 theta • theta‖) |inner ℝ x0 theta| ≤ 2
    exact max_le (max_le (by rw [htheta]; norm_num) ho) (hm.trans (by norm_num))
  change dist _ 0 ≤ 2
  rw [dist_zero_right]
  exact (contractLine_norm_le _).trans hb

end NativeCoarseRepresentativeGeometry
