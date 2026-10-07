import Theorems.Thm_StickyKakeya4_native_retained_fine_pair_density
import Theorems.Thm_StickyKakeya4_native_reference_hereditary_upper

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeSpatialParentCount
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeJointUniformCoarseRelations
open NativeRawPointSourceProfiles NativeRawPointGlobalProfiles NativeFullCoarseShadow
open NativeCoarsePointMultiplicity NativeMiddleWindowBalance NativeCoarseShadingCapacity
open NativeRetainedFinePairDensity NativeSpatialAngularGeometry NativeRawShadowPointComparison
open NativeConditionedPairMenu NativeAllTwoScaleConfiguration NativeTwoScaleConfiguration
open NativeFixedCompactKakeyaExponent
open NativeConditionalCoarseInterpolation

/-- A literal raw cell contains at most one raw label. -/
lemma raw_point_count_le_one {n : ℕ} (D : FiniteScaleSource n)
    (E : Finset (Fin n × Index)) (f : ℕ) (v : Index)
    (hv : ∀z∈E,spatialLabel D (2^f) z.2=v) : rawPointCount D E f ≤ 1 := by
  apply card_le_one.mpr
  intro x hx y hy
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hy
  exact (hv z hz).trans (hv w hw).symm

/-- Inside one raw cell, actual full-shadow multiplicity controls the
number of genuine pair labels with the fixed 2401 point-menu cost. -/
theorem fine_pair_count_in_raw_cell {n level : ℕ} {D : FiniteScaleSource n}
    {eta zeta a : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n))
    (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (E : Finset (Fin n × Index)) (hE : E⊆NativeCoarseShadingCapacity.retained original R)
    (f : ℕ) (hf : f ≤ level) (v : Index)
    (hv : ∀z∈E,spatialLabel D (2^f) z.2=v)
    (U : ℝ) (hU : 0 ≤ U)
    (hupper : (NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level f E)).toReal ≤ U) :
    (finePairCount h R E a level f:ℝ) ≤ 2401*U := by
  have hR : ∀z∈E,z.1∈R := fun z hz => (mem_filter.mp (hE hz)).2
  have hOld : E⊆incidences original := hE.trans (filter_subset _ _)
  have hpoint := (same_R_point_image_card_comparison h original Hbackbone.1 Hbackbone.2.2.1
    R E hOld hR level f Hbackbone.2.1 hf).1
  have hraw := raw_point_count_le_one D E f v hv
  have hp : shadowPointCount h R E a level f ≤ 2401 := by
    exact hpoint.trans (by simpa only [rawPointCount,Nat.mul_one] using Nat.mul_le_mul_left 2401 hraw)
  by_cases hEn : E.Nonempty
  · have hp0 : (0:ℝ) < shadowPointCount h R E a level f := by
      exact_mod_cast card_pos.mpr (hEn.image _)
    rw [full_source_multiplicity_real h R a level f E hR] at hupper
    simp only [NativeIncidenceMultiplicityTower.multiplicity,coarse,image_image,Function.comp_def] at hupper
    change (finePairCount h R E a level f:ℝ)/(shadowPointCount h R E a level f:ℝ) ≤ U at hupper
    have hh := (div_le_iff₀ hp0).mp hupper
    calc
      _ ≤ U*(shadowPointCount h R E a level f:ℝ) := hh
      _ ≤ U*2401 := mul_le_mul_of_nonneg_left (by exact_mod_cast hp) hU
      _ = _ := by ring
  · rw [not_nonempty_iff_eq_empty.mp hEn]
    simpa only [finePairCount,image_empty,card_empty,Nat.cast_zero] using
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2401) hU)

/-- The parent labels are the first coordinates of these actual pairs. -/
lemma parent_count_le_pair_count {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level f : ℕ) :
    (E.image (fun z => parentLabel D a (2^f) z.1)).card ≤ finePairCount h R E a level f := by
  have hh := card_image_le (s:=E.image (physicalPair h R a level f)) (f:=Prod.fst)
  simpa only [image_image,Function.comp_def,physicalPair_parent,finePairCount] using hh

/-- The master's actual fields give a global upper for every literal subset.
The depth-zero parent tax is preserved explicitly. -/
theorem source_global_subset_upper {n d g level : ℕ} {D : FiniteScaleSource n}
    {eta zeta a seed tau : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n))
    (E1 : Finset (Fin n × Index)) (L : ℕ)
    (schedule : Fin (g+1) → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (htau : 0 < tau) (heta : 0 ≤ eta) (hseed : seed ≤ tau/16384)
    (hg : 0 < g) (hgl : g ≤ level)
    (hgrid : 1/(g:ℝ) < min (boundaryWindow tau) ((tau/16)/1000)/4)
    (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (hschedule : schedule=fullSchedule tau htau g level)
    (Hcore : IsCore D original R a eta zeta d (g+1) L Rel
      (fun j => 2^(schedule j).val) E1)
    (hcost : (125*175616*16384:ℝ)*(factor d (g+1) L:ℝ)*(coreRadix original R L:ℝ)^2*
      D.thickness^(-eta) ≤ D.thickness^(-(seed/8)))
    (hconditioned : ∀i j,HasUniformFibers E1 (coreRadix original R L)
        (conditionedGlobalPair h R a level (schedule i).val (schedule j).val) ∧
      HasUniformFibers E1 (coreRadix original R L)
        (conditionedGlobalPoint h R a level (schedule i).val (schedule j).val))
    (hreference : ∀m f : ℕ,m ≤ f → f ≤ level → HasConditionalTwoScale h R E1 a level m f tau)
    (S : Finset (Fin n × Index)) (hS : S⊆E1) (c : ℕ) (hc : c ≤ level) :
    (NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level c S)).toReal ≤
      (373248*D.thickness^(-zeta))*(D.thickness^(-(3*tau))*
        (1/((2^c:ℕ):ℝ))^(-extremalExponent)) := by
  have hHer := NativeReferenceHereditaryUpper.from_master_reference h original R E1 schedule Rel
    htau heta hseed hg hgl hgrid Hbackbone hschedule Hcore hcost hconditioned hreference
  have hR : ∀z∈S,z.1∈R := fun z hz => (mem_filter.mp (Hcore.1 (hS hz))).2
  have hpop := Hbackbone.2.2.2.2.2.2.2.2
  have hratio : (64/((2^c:ℕ):ℝ))/(64/((1:ℕ):ℝ))=1/((2^c:ℕ):ℝ) := by norm_num; ring
  apply global_shadow_multiplicity_upper h R S hR level c
    (by
      intro p hp
      simpa using (hpop ⟨0,by omega⟩ p hp).1)
    _ (by have hd := h.1.2.1; positivity)
  intro p _hp
  simpa only [pow_zero,hratio] using hHer S hS 0 c (Nat.zero_le _) hc p

/-- At the selected parent radius, each actual spatial node sees only this
many original phase parents. Grain classes inside that node inherit the bound. -/
theorem source_spatial_parent_count {n d g level : ℕ} {D : FiniteScaleSource n}
    {eta zeta a seed tau : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n))
    (E1 : Finset (Fin n × Index)) (L : ℕ)
    (schedule : Fin (g+1) → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (htau : 0 < tau) (heta : 0 ≤ eta) (hseed : seed ≤ tau/16384)
    (hg : 0 < g) (hgl : g ≤ level)
    (hgrid : 1/(g:ℝ) < min (boundaryWindow tau) ((tau/16)/1000)/4)
    (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (hschedule : schedule=fullSchedule tau htau g level)
    (Hcore : IsCore D original R a eta zeta d (g+1) L Rel
      (fun j => 2^(schedule j).val) E1)
    (hcost : (125*175616*16384:ℝ)*(factor d (g+1) L:ℝ)*(coreRadix original R L:ℝ)^2*
      D.thickness^(-eta) ≤ D.thickness^(-(seed/8)))
    (hconditioned : ∀i j,HasUniformFibers E1 (coreRadix original R L)
        (conditionedGlobalPair h R a level (schedule i).val (schedule j).val) ∧
      HasUniformFibers E1 (coreRadix original R L)
        (conditionedGlobalPoint h R a level (schedule i).val (schedule j).val))
    (hreference : ∀m f : ℕ,m ≤ f → f ≤ level → HasConditionalTwoScale h R E1 a level m f tau)
    (S : Finset (Fin n × Index)) (hS : S⊆E1) (c : ℕ) (hc : c ≤ level)
    (v : Index) (hv : ∀z∈S,spatialLabel D (2^c) z.2=v) :
    ((S.image (fun z => parentLabel D a (2^c) z.1)).card:ℝ) ≤
      2401*((373248*D.thickness^(-zeta))*(D.thickness^(-(3*tau))*
        (1/((2^c:ℕ):ℝ))^(-extremalExponent))) := by
  have hu := source_global_subset_upper h original R E1 L schedule Rel htau heta hseed hg hgl hgrid
    Hbackbone hschedule Hcore hcost hconditioned hreference S hS c hc
  have hh := fine_pair_count_in_raw_cell h original R Hbackbone S (hS.trans Hcore.1)
    c hc v hv _ (by have hd := h.1.2.1; positivity) hu
  exact (show ((S.image (fun z => parentLabel D a (2^c) z.1)).card:ℝ) ≤
      (finePairCount h R S a level c:ℝ) by
    exact_mod_cast parent_count_le_pair_count h R S a level c).trans hh

end NativeSpatialParentCount
