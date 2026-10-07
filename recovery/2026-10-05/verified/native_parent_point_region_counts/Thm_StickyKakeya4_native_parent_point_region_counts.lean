import Theorems.Thm_StickyKakeya4_native_raw_point_rank_four_ratio
import Theorems.Thm_StickyKakeya4_native_actual_angular_menu_lower
import Theorems.Thm_StickyKakeya4_native_coarse_shading_uniformity

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeParentPointRegionCounts
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations NativeConditionedPairMenu
open NativeBalancedConfiguration NativeIncidenceMultiplicityTower NativeActualAngularMenuLower
open NativeOriginalCoarseTupleMenu NativeCoarseShadingUniformity
open scoped BigOperators

/-- A region cuts whole original point fibers of its specified edge family. -/
def regionEdges {T X : Type*} (E : Finset (T × X)) (test : X → Prop) : Finset (T × X) :=
  E.filter (fun z => test z.2)

/-- Distinct occupied original points in that same literal region. -/
def regionPoints {T X : Type*} [DecidableEq X] (E : Finset (T × X))
    (test : X → Prop) : Finset X := (E.image Prod.snd).filter test

lemma region_points_image {T X : Type*} [DecidableEq X] (E : Finset (T × X)) (test : X → Prop) :
    (regionEdges E test).image Prod.snd=regionPoints E test := by
  rw [regionPoints,filter_image]
  rfl

/-- Exact mass readback uses the selected parent's own point weights,
never the all-E2 weights that preceded its phase-parent restriction. -/
lemma region_card_fiber_sum {T X : Type*} [DecidableEq X] (E : Finset (T × X))
    (test : X → Prop) :
    (regionEdges E test).card=∑k∈regionPoints E test,(E.filter (fun z => z.2=k)).card := by
  rw [card_eq_sum_card_image Prod.snd,region_points_image]
  apply sum_congr rfl
  intro k hk
  have htest := (mem_filter.mp hk).2
  congr 1
  ext z
  simp only [regionEdges,mem_filter]
  constructor
  · exact fun hh => ⟨hh.1.1,hh.2⟩
  · intro hh
    exact ⟨⟨hh.1,hh.2 ▸ htest⟩,hh.2⟩

/-- Every literal region of an unchanged uniform reference has its actual
incidence mass comparable to its distinct point population. -/
theorem uniform_region_counts {T X : Type*} [DecidableEq T] [DecidableEq X]
    (E : Finset (T × X)) (Q : ℕ) (H : HasUniformFibers E Q Prod.snd) (test : X → Prop) :
    multiplicity E*(regionPoints E test).card ≤ (Q:ℝ)^2*(regionEdges E test).card ∧
    (regionEdges E test).card ≤ (Q:ℝ)^2*multiplicity E*(regionPoints E test).card := by
  have hs : ((regionEdges E test).card:ℝ)=
      ∑k∈regionPoints E test,((E.filter (fun z => z.2=k)).card:ℝ) := by
    exact_mod_cast region_card_fiber_sum E test
  constructor
  · calc
      _ = ∑_k∈regionPoints E test,multiplicity E := by simp [mul_comm]
      _ ≤ ∑k∈regionPoints E test,(Q:ℝ)^2*((E.filter (fun z => z.2=k)).card:ℝ) :=
        sum_le_sum (fun k hk => mean_le_point_fiber E Q H k (mem_filter.mp hk).1)
      _ = _ := by rw [←mul_sum,←hs]
  · rw [hs]
    calc
      _ ≤ ∑_k∈regionPoints E test,(Q:ℝ)^2*multiplicity E :=
        sum_le_sum (fun k _hk => NativeRankOneReferenceUpper.point_degree_le_reference_mean E Q H k)
      _ = _ := by simp; ring

/-- Any later edge cut inherits only the reference point-weight upper.
Its occupied point count is computed after that cut. -/
theorem subset_region_upper {T X : Type*} [DecidableEq T] [DecidableEq X]
    (E F : Finset (T × X)) (hFE : F⊆E) (Q : ℕ)
    (H : HasUniformFibers E Q Prod.snd) (test : X → Prop) :
    ((regionEdges F test).card:ℝ) ≤ (Q:ℝ)^2*multiplicity E*(regionPoints F test).card := by
  have hs : ((regionEdges F test).card:ℝ)=
      ∑k∈regionPoints F test,((F.filter (fun z => z.2=k)).card:ℝ) := by
    exact_mod_cast region_card_fiber_sum F test
  rw [hs]
  calc
    _ ≤ ∑_k∈regionPoints F test,(Q:ℝ)^2*multiplicity E := by
      apply sum_le_sum
      intro k _hk
      have hc : ((F.filter (fun z => z.2=k)).card:ℝ) ≤ (E.filter (fun z => z.2=k)).card := by
        exact_mod_cast card_le_card (filter_subset_filter _ hFE)
      exact hc.trans (NativeRankOneReferenceUpper.point_degree_le_reference_mean E Q H k)
    _ = _ := by simp; ring

/-- A lower point population after an arbitrary cut is charged to actual
retention in this particular region. Global retention is not substituted. -/
theorem region_point_retention {T X : Type*} [DecidableEq T] [DecidableEq X]
    (E F : Finset (T × X)) (hFE : F⊆E) (Q : ℕ)
    (H : HasUniformFibers E Q Prod.snd) (test : X → Prop)
    (lambda G : ℝ) (hlambda : 0 ≤ lambda) (hG : 0 ≤ G)
    (hret : lambda*(regionEdges E test).card ≤ G*(regionEdges F test).card) :
    lambda*multiplicity E*(regionPoints E test).card ≤
      G*(Q:ℝ)^4*multiplicity E*(regionPoints F test).card := by
  have hlo := (uniform_region_counts E Q H test).1
  have hhi := subset_region_upper E F hFE Q H test
  calc
    _ = lambda*(multiplicity E*(regionPoints E test).card) := by ring
    _ ≤ lambda*((Q:ℝ)^2*(regionEdges E test).card) := mul_le_mul_of_nonneg_left hlo hlambda
    _ = (Q:ℝ)^2*(lambda*(regionEdges E test).card) := by ring
    _ ≤ (Q:ℝ)^2*(G*(regionEdges F test).card) := mul_le_mul_of_nonneg_left hret (sq_nonneg _)
    _ = ((Q:ℝ)^2*G)*(regionEdges F test).card := by ring
    _ ≤ ((Q:ℝ)^2*G)*((Q:ℝ)^2*multiplicity E*(regionPoints F test).card) :=
      mul_le_mul_of_nonneg_left hhi (by positivity)
    _ = _ := by ring

/-- The actual E1 core already installs the formal parent/microcell
relation at every scheduled depth. -/
theorem core_parent_point_uniformity {n d g level : ℕ} {D : FiniteScaleSource n}
    {eta zeta a : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n)) (E : Finset (Fin n × Index))
    (L : ℕ) (schedule : Fin g → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : IsCore D original R a eta zeta (menuSize d g) g L
      (relationMenu h R a schedule Rel) (fun j => 2^(schedule j).val) E)
    (j : Fin g) (p : Parent) :
    HasUniformFibers (parentEdges D a (2^(schedule j).val) E p) (coreRadix original R L) Prod.snd := by
  apply formal_uniform_in_parent D E a (schedule j).val (coreRadix original R L) _ p
  intro x hx y hy
  simpa only [relationMenu,Fin.addCases_right,unit_degree_eq_fiber] using
    H.2.2.2.1 (Fin.natAdd d (Fin.natAdd g (Fin.natAdd g j))) x y hx hy

/-- Same-source occupied-region bounds in one literal scheduled coarse
phase parent. Later E2/source-point cuts receive only the last upper bound. -/
theorem source_parent_region_counts {n d g level : ℕ} {D : FiniteScaleSource n}
    {eta zeta a seed : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n)) (E1 : Finset (Fin n × Index))
    (L : ℕ) (schedule : Fin g → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : IsCore D original R a eta zeta (menuSize d g) g L
      (relationMenu h R a schedule Rel) (fun j => 2^(schedule j).val) E1)
    (j : Fin g) (HB : HasBalancedScale h R E1 a level (schedule j).val seed)
    (p : Parent) (hp : (parentEdges D a (2^(schedule j).val) E1 p).Nonempty)
    (test : Index → Prop) :
    let I := parentEdges D a (2^(schedule j).val) E1 p
    let Q := coreRadix original R L
    let eps := ((2^(schedule j).val:ℕ):ℝ)*D.thickness/64
    D.thickness^seed*eps^(-NativeFixedCompactKakeyaExponent.extremalExponent)*(regionPoints I test).card ≤
      (Q:ℝ)^2*(regionEdges I test).card ∧
    (regionEdges I test).card ≤ (Q:ℝ)^2*(D.thickness^(-seed)*eps^(-NativeFixedCompactKakeyaExponent.extremalExponent))*
      (regionPoints I test).card ∧
    ∀F⊆I,((regionEdges F test).card:ℝ) ≤
      (Q:ℝ)^2*(D.thickness^(-seed)*eps^(-NativeFixedCompactKakeyaExponent.extremalExponent))*
        (regionPoints F test).card := by
  have hU := core_parent_point_uniformity h original R E1 L schedule Rel H j p
  obtain ⟨_hSlo,_hShi,hMlo,hMhi⟩ := HB.2.2 p hp
  have hRegion := uniform_region_counts _ _ hU test
  refine ⟨?_,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_right hMlo (Nat.cast_nonneg _)).trans hRegion.1
  · exact hRegion.2.trans (by gcongr)
  · intro F hF
    exact (subset_region_upper _ F hF _ hU test).trans (by gcongr)

end NativeParentPointRegionCounts
