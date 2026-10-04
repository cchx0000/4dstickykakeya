import Theorems.Thm_StickyKakeya4_native_angular_chart_selection
import Theorems.Thm_StickyKakeya4_native_separated_fractional_patches
import Theorems.Thm_StickyKakeya4_parent_all_real_tube_control
import Theorems.Thm_StickyKakeya4_working_scale_profile_budget
import Theorems.Thm_StickyKakeya4_actual_scalar_ad_profiles

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace NativeOriginalParentAssembly

open NativeDyadicTubeStopping NativeDyadicTubeEpoch NativeParentSpines
open NativeAngularChartSelection ActualTubeFootprintProfiles DisjointProfileEpochs
open NativeSeparatedFractionalPatches ParentAllRealTubeControl
open ShearedGridADReference ShearedGridTubeReference ShearedGridSpineColumns
open NativeContactFractionalComposition NativeFractionalReferenceComposition
open SmallFiberAlignment FractionalFiberAlignment SelfUniform
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The source labels remain original points; only their geometric coordinates
are permuted into the selected genuine tube chart. -/
def chartPosition (A : Finset Plane) (j : Fin 2) : A → Plane :=
  chartPoint j ∘ position A

lemma chartPosition_injective (A : Finset Plane) (j : Fin 2) :
    Function.Injective (chartPosition A j) :=
  (chartPoint_injective j).comp Subtype.val_injective

lemma chartPosition_mem (A : Finset Plane) (j : Fin 2) (q : A) :
    chartPosition A j q ∈ A.image (chartPoint j) :=
  Finset.mem_image_of_mem _ q.property

lemma chartPosition_grid_card (A : Finset Plane) (j : Fin 2) (S : Finset A) (r : ℝ) :
    (((S.image (chartPosition A j)).image (ADGridCoverMenus.gridLabel r)).card) =
      (S.image (grid (position A) r)).card := by
  rw [Finset.image_image]
  exact chart_grid_card j (position A) r S

lemma chartPosition_same_cell (A : Finset Plane) (j : Fin 2) (r : ℝ) (q z : A)
    (h : grid (position A) r q = grid (position A) r z) :
    ADGridCoverMenus.gridLabel r (chartPosition A j q) =
      ADGridCoverMenus.gridLabel r (chartPosition A j z) := by
  change grid (chartPoint j ∘ position A) r q = grid (chartPoint j ∘ position A) r z
  rw [chart_grid, chart_grid, h]

/-- An actual ORIGINAL parent, before coordinate permutation. -/
def parent (A : Finset Plane) (B : Finset A) (b : ℝ) (c : GridLabel 1) : Finset A :=
  B.filter (fun q => grid (position A) b q = c)

lemma parent_subset (A : Finset Plane) (B : Finset A) (b : ℝ) (c : GridLabel 1) :
    parent A B b c ⊆ B := Finset.filter_subset _ _

lemma parent_chart_span (A : Finset Plane) (B : Finset A) (j : Fin 2)
    {b : ℝ} (hb : 0 < b) (c : GridLabel 1) :
    ∀ p ∈ (parent A B b c).image (chartPosition A j),
      (c j : ℝ) * b ≤ p 0 ∧ p 0 ≤ (c j : ℝ) * b + b := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  have hcell := (Finset.mem_filter.mp hq).2
  have hbounds := SeparatedAlignmentPatches.cell_bounds b hb (position A q) j
  have he : SeparatedAlignmentPatches.cell b (position A q) j = c j := congrFun hcell j
  rw [he] at hbounds
  change (c j : ℝ) * b ≤ chartPoint j (position A q) 0 ∧
    chartPoint j (position A q) 0 ≤ (c j : ℝ) * b + b
  rw [chartPoint_zero]
  exact ⟨hbounds.1, by nlinarith only [hbounds.2]⟩

lemma parent_chart_diameter (A : Finset Plane) (B : Finset A) (j : Fin 2)
    {b : ℝ} (hb : 0 < b) (c : GridLabel 1) :
    ∀ p ∈ (parent A B b c).image (chartPosition A j),
      ∀ q ∈ (parent A B b c).image (chartPosition A j), dist p q ≤ b := by
  intro p hp q hq
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
  rw [chartPosition, Function.comp_apply, Function.comp_apply, chartPoint_dist]
  exact (SeparatedAlignmentPatches.same_cell_dist_lt b hb (position A u) (position A v)
    ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm)).le

lemma parent_image_subset (A : Finset Plane) (B E : Finset A) (j : Fin 2)
    (b : ℝ) (c : GridLabel 1) (hBE : B ⊆ E) :
    (parent A B b c).image (chartPosition A j) ⊆ E.image (chartPosition A j) :=
  Finset.image_subset_image ((parent_subset A B b c).trans hBE)

/-- Actual contact witnesses produced by the angular constructor give genuine
physical spines in each ORIGINAL parent. Their width remains exactly 2rho. -/
theorem physical_contacts (A : Finset Plane) (Fs : List (Finset A))
    (B Ω : Finset A) (hΩ : Ω ⊆ B) (hB : B ⊆ support Fs)
    (T : Finset A → TubeData 1) (j : Fin 2)
    (hchart : ∀ F ∈ Fs, |(T F).direction j| = 1)
    (a b ρ τ γ ell s : ℝ) (angle : GridLabel 1 → ℝ)
    (hwitness : ∀ q ∈ Ω, ∃ z ∈ Ω,
      grid (position A) a z = grid (position A) a q ∧
      |chartSlope j (T (owner Fs z)) - angle (grid (position A) b q)| ≤ γ ∧
      InTube (T (owner Fs z)) (2 * ρ) τ (position A z) ∧
      (∀ r ∈ parentSpine A Fs B b z, r ∈ B ∧
        grid (position A) b r = grid (position A) b q ∧
        InTube (T (owner Fs z)) (2 * ρ) τ (position A r)) ∧
      ell * (b / ρ) ^ s ≤ (((parentSpine A Fs B b z).image (grid (position A) ρ)).card : ℝ))
    (hnested : ∀ q z : A, grid (position A) a z = grid (position A) a q →
      grid (position A) b z = grid (position A) b q) (c : GridLabel 1) :
    ∃ S : Plane → Finset Plane, ∃ U : Plane → TubeData 1,
      (∀ q ∈ (parent A Ω b c).image (chartPosition A j),
        S q ⊆ (parent A B b c).image (chartPosition A j)) ∧
      (∀ q ∈ (parent A Ω b c).image (chartPosition A j),
        ell * (b / ρ) ^ s ≤ (((S q).image (ADGridCoverMenus.gridLabel ρ)).card : ℝ)) ∧
      (∀ q ∈ (parent A Ω b c).image (chartPosition A j), |(U q).direction 0| = 1) ∧
      (∀ q ∈ (parent A Ω b c).image (chartPosition A j), |slope (U q) - angle c| ≤ γ) ∧
      (∀ q ∈ (parent A Ω b c).image (chartPosition A j),
        ∃ z ∈ (parent A B b c).image (chartPosition A j),
          ADGridCoverMenus.gridLabel a z = ADGridCoverMenus.gridLabel a q ∧
          InTube (U q) (2 * ρ) τ z) ∧
      (∀ q ∈ (parent A Ω b c).image (chartPosition A j),
        ∀ p ∈ S q, InTube (U q) (2 * ρ) τ p) := by
  classical
  have hex : ∀ q ∈ (parent A Ω b c).image (chartPosition A j),
      ∃ S : Finset Plane, ∃ U : TubeData 1,
        S ⊆ (parent A B b c).image (chartPosition A j) ∧
        ell * (b / ρ) ^ s ≤ ((S.image (ADGridCoverMenus.gridLabel ρ)).card : ℝ) ∧
        |U.direction 0| = 1 ∧ |slope U - angle c| ≤ γ ∧
        (∃ z ∈ (parent A B b c).image (chartPosition A j),
          ADGridCoverMenus.gridLabel a z = ADGridCoverMenus.gridLabel a q ∧ InTube U (2 * ρ) τ z) ∧
        (∀ p ∈ S, InTube U (2 * ρ) τ p) := by
    intro q hq
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨huΩ, huc⟩ := Finset.mem_filter.mp hu
    obtain ⟨z, hz, hcell, hslope, hTube, hspine, hrich⟩ := hwitness u huΩ
    refine ⟨(parentSpine A Fs B b z).image (chartPosition A j),
      chartTube j (T (owner Fs z)), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr
        ⟨(hspine r hr).1, (hspine r hr).2.1.trans huc⟩)
    · rwa [chartPosition_grid_card]
    · exact chartTube_unit_zero j _ (hchart _ (owner_spec Fs (hB (hΩ hz))).1)
    · simpa only [huc, chartSlope, ShearedGridSpineColumns.slope] using hslope
    · refine ⟨chartPosition A j z, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr
        ⟨hΩ hz, (hnested u z hcell).trans huc⟩), chartPosition_same_cell A j a z u hcell, ?_⟩
      exact (chart_inTube_iff j _ _ _ _).mpr hTube
    · intro p hp
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
      exact (chart_inTube_iff j _ _ _ _).mpr (hspine r hr).2.2
  choose S U hspec using hex
  let S' : Plane → Finset Plane := fun q =>
    if hq : q ∈ (parent A Ω b c).image (chartPosition A j) then S q hq else ∅
  let U' : Plane → TubeData 1 := fun q =>
    if hq : q ∈ (parent A Ω b c).image (chartPosition A j) then U q hq
    else ⟨0, axisDirection 1, axisDirection_unit 1⟩
  refine ⟨S', U', ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intro q hq
  · simpa only [S', dif_pos hq] using (hspec q hq).1
  · simpa only [S', dif_pos hq] using (hspec q hq).2.1
  · simpa only [U', dif_pos hq] using (hspec q hq).2.2.1
  · simpa only [U', dif_pos hq] using (hspec q hq).2.2.2.1
  · simpa only [U', dif_pos hq] using (hspec q hq).2.2.2.2.1
  · simpa only [S', U', dif_pos hq] using (hspec q hq).2.2.2.2.2

end
end NativeOriginalParentAssembly
