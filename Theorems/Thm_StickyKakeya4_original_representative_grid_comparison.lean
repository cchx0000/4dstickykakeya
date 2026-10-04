import Theorems.Thm_StickyKakeya4_ad_grid_cover_menus
import Theorems.Thm_StickyKakeya4_euclidean_alignment_patches
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalRepresentativeGridComparison
open Classical Finset ADGridCoverMenus FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
abbrev Plane := Fin 2 → ℝ
abbrev Label := Fin 2 → ℤ
def neighbors (k : Label) : Finset Label := Fintype.piFinset fun i => Icc (k i-1) (k i+1)
lemma neighbors_card (k : Label) : (neighbors k).card=9 := by
  have hi (i : Fin 2) : (Icc (k i-1) (k i+1)).card=3 := by
    have hh : ((Icc (k i-1) (k i+1)).card:ℤ)=3 := by
      rw [Int.card_Icc_of_le _ _ (by omega)]
      omega
    exact_mod_cast hh
  simp [neighbors,Fintype.card_piFinset,hi]
/-- Keeping one original point in every fine occupied cell controls the
 ORIGINAL coarse grid image, even when the representatives are not separated. -/
theorem original_coarse_grid_comparison (Y R : Finset Plane) {delta q : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q)
    (himage : R.image (gridLabel delta)=Y.image (gridLabel delta)) :
    (Y.image (gridLabel q)).card ≤ 9*(R.image (gridLabel q)).card := by
  have hq : 0 < q := hd.trans_le hdq
  have hsub : Y.image (gridLabel q) ⊆ (R.image (gridLabel q)).biUnion neighbors := by
    intro k hk
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hk
    have hpgrid : gridLabel delta p ∈ R.image (gridLabel delta) := by
      rw [himage]
      exact mem_image_of_mem _ hp
    obtain ⟨r,hr,hgrid⟩ := mem_image.mp hpgrid
    have hdist : dist p r ≤ q :=
      (SeparatedAlignmentPatches.same_cell_dist_lt delta hd p r hgrid.symm).le.trans hdq
    exact mem_biUnion.mpr ⟨gridLabel q r,mem_image_of_mem _ hr,gridLabel_mem_netBox hq hdist⟩
  have hc := (card_le_card hsub).trans
    (card_biUnion_le_card_mul (R.image (gridLabel q)) neighbors 9 (fun k _hk => (neighbors_card k).le))
  simpa only [Nat.mul_comm] using hc
/-- Point-AD transports along a genuine isometry, with exact original ball
 cardinalities. This is used only to change the coordinate presentation. -/
theorem point_AD_isometric_image {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [DecidableEq Y]
    (e : X ≃ᵢ Y) (A : Finset X) {delta K t : ℝ} (hAD : ADBounds A delta K t) :
    ADBounds (A.image e) delta K t := by
  intro a ha r hr hR
  obtain ⟨c,hc,rfl⟩ := mem_image.mp ha
  have hball : carrierBall (A.image e) (e c) r=(carrierBall A c r).image e := by
    ext y
    constructor
    · intro hy
      obtain ⟨hyA,hyD⟩ := (mem_carrierBall (A.image e) y (e c) r).mp hy
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hyA
      exact mem_image.mpr ⟨x,(mem_carrierBall A x c r).mpr ⟨hx,by simpa only [e.dist_eq] using hyD⟩,rfl⟩
    · intro hy
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
      obtain ⟨hxA,hxD⟩ := (mem_carrierBall A x c r).mp hx
      exact (mem_carrierBall (A.image e) (e x) (e c) r).mpr
        ⟨mem_image_of_mem _ hxA,by simpa only [e.dist_eq] using hxD⟩
  rw [hball,card_image_of_injective _ e.injective]
  exact hAD c hc r hr hR
/-- Coordinate presentation used by the phase caller, as a genuine isometry. -/
def toPair : Plane ≃ᵢ (ℝ × ℝ) := IsometryEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
lemma pair_image_readback (Y : Finset (ℝ × ℝ)) : (Y.image toPair.symm).image toPair=Y := by
  rw [image_image]
  have hh : (toPair ∘ toPair.symm : (ℝ × ℝ) → (ℝ × ℝ))=id := by
    funext x
    exact toPair.apply_symm_apply x
  rw [hh,image_id]
lemma pair_grid_image (Y : Finset Plane) (q : ℝ) :
    NativeTangentGridCoarsening.planarCells (Y.image toPair) id q=
      (Y.image (gridLabel q)).image (finTwoArrowEquiv ℤ) := by
  simp only [NativeTangentGridCoarsening.planarCells,image_image]
  rfl
lemma pair_grid_card (Y : Finset Plane) (q : ℝ) :
    (NativeTangentGridCoarsening.planarCells (Y.image toPair) id q).card=(Y.image (gridLabel q)).card := by
  rw [pair_grid_image,card_image_of_injective _ (finTwoArrowEquiv ℤ).injective]
/-- Original Y coordinates and representative coordinates are kept exactly
 when returning to the phase caller's product-space convention. -/
theorem pair_representative_readback (Y : Finset (ℝ × ℝ)) (R : Finset Plane) {delta K t : ℝ}
    (hR : R ⊆ Y.image toPair.symm) (hAD : ADBounds R delta K t) :
    R.image toPair ⊆ Y ∧ ADBounds (R.image toPair) delta K t := by
  constructor
  · have hh := image_subset_image hR (f := toPair)
    rwa [pair_image_readback] at hh
  · exact point_AD_isometric_image toPair R hAD
end OriginalRepresentativeGridComparison
