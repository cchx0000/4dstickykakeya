import Theorems.Thm_StickyKakeya4_native_cover_ad_representatives
import Theorems.Thm_StickyKakeya4_original_representative_grid_comparison
import Theorems.Thm_StickyKakeya4_original_planar_ad_grid_population
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section
namespace OriginalLiteralGrainProfiles
open Classical Finset FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening NativeTangentGridCoarsening
open OriginalRepresentativeGridComparison
/-- Literal Euclidean delta-cover AD of original grain coordinates, merely
 presented as functions on Fin 2 for the already checked Euclidean API. -/
def LiteralCoverAD (Y : Finset (ℝ × ℝ)) (delta K t : ℝ) : Prop :=
  NativeEuclideanCoverInput.EuclideanCoverAD (Y.image toPair.symm) delta K t
/-- Fine-cover lower mass is already a lower bound on the ORIGINAL grain
 cardinality. No separation or point-count AD of Y is used. -/
theorem original_grain_mass_lower (Y : Finset (ℝ × ℝ)) (hY : Y.Nonempty)
    {delta K t : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1) (hK : 0 < K)
    (H : LiteralCoverAD Y delta K t) : 1 ≤ K*delta^t*(Y.card:ℝ) := by
  obtain ⟨g,hg⟩ := hY
  have hl := (H (toPair.symm g) (mem_image_of_mem _ hg) 1 hd1 le_rfl).1
  have hc : NativeEuclideanCoverInput.ecover (Y.image toPair.symm) delta (toPair.symm g) 1 ≤ (Y.card:ℝ) := by
    unfold NativeEuclideanCoverInput.ecover NativeEuclideanCoverInput.eball
    have hh : (((NativeEuclideanCoverInput.eball (Y.image toPair.symm) (toPair.symm g) 1).image
        (ADGridCoverMenus.gridLabel delta)).card) ≤ (Y.image toPair.symm).card :=
      (Finset.card_image_le).trans (card_le_card (filter_subset _ _))
    rw [card_image_of_injective _ toPair.symm.injective] at hh
    exact_mod_cast hh
  have hh := hl.trans hc
  rw [Real.div_rpow (by norm_num : (0:ℝ)≤1) hd.le,Real.one_rpow,div_div] at hh
  have hp : 0 < delta^t*K := mul_pos (Real.rpow_pos_of_pos hd t) hK
  have hcross := (div_le_iff₀ hp).mp hh
  nlinarith only [hcross]
/-- Actual original representatives supply point AD; they are only an
 intermediate counting device, and all original coarse grid cells are charged. -/
theorem exists_original_grain_representatives (Y : Finset (ℝ × ℝ)) (hY : Y.Nonempty)
    {delta K t : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1) (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hbox : ∀ g ∈ Y, ‖g‖ ≤ 1) (H : LiteralCoverAD Y delta K t) :
    ∃ R : Finset (ℝ × ℝ), R ⊆ Y ∧ R.Nonempty ∧ ADBounds R delta (100*K) t ∧
      ∀ q : ℝ, delta ≤ q →
        (planarCells Y id q).card ≤ 9*(planarCells R id q).card := by
  have hboxFn : ∀ p ∈ Y.image toPair.symm, ∀ i : Fin 2, |p i| ≤ 1 := by
    intro p hp i
    obtain ⟨g,hg,rfl⟩ := mem_image.mp hp
    have hh := max_le_iff.mp (hbox g hg)
    fin_cases i
    · change |g.1| ≤ 1
      exact hh.1
    · change |g.2| ≤ 1
      exact hh.2
  obtain ⟨R,hRY,himage,_hinj,hAD⟩ := NativeCoverADRepresentatives.original_representatives_AD
    hd hd1 hK ht ht2 hboxFn H
  have hRne : R.Nonempty := by
    obtain ⟨g,hg⟩ := hY
    have hcell : ADGridCoverMenus.gridLabel delta (toPair.symm g) ∈ R.image (ADGridCoverMenus.gridLabel delta) := by
      rw [himage]
      exact mem_image_of_mem _ (mem_image_of_mem _ hg)
    obtain ⟨r,hr,_⟩ := mem_image.mp hcell
    exact ⟨r,hr⟩
  have hpair := pair_representative_readback Y R hRY hAD
  refine ⟨R.image toPair,hpair.1,hRne.image _,hpair.2,?_⟩
  intro q hdq
  have hh := original_coarse_grid_comparison (Y.image toPair.symm) R hd hdq himage
  have hYcard := pair_grid_card (Y.image toPair.symm) q
  rw [pair_image_readback] at hYcard
  rw [hYcard,pair_grid_card]
  exact hh
/-- The literal original cover-AD profile controls the FULL original q-grid
 image. Original Y need not be separated, and no coarse profile is assumed. -/
theorem original_literal_grain_grid_mass (Y : Finset (ℝ × ℝ)) (hY : Y.Nonempty)
    {delta q K t : ℝ} (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hbox : ∀ g ∈ Y, ‖g‖ ≤ 1) (H : LiteralCoverAD Y delta K t) :
    q^t*((planarCells Y id q).card:ℝ) ≤ 207360000*K^2 := by
  obtain ⟨R,hRY,hR,hAD,hgrid⟩ := exists_original_grain_representatives Y hY hd (hdq.trans hq1) hK ht ht2 hbox H
  have hK' : 1 ≤ 100*K := by linarith only [hK]
  have hm := OriginalPlanarADGridPopulation.original_planar_grid_mass R hR hd hdq hq1 hK' ht ht2
    (fun g hg => hbox g (hRY hg)) hAD
  have hc : ((planarCells Y id q).card:ℝ) ≤ 9*((planarCells R id q).card:ℝ) := by
    exact_mod_cast hgrid q hdq
  have hq := hd.trans_le hdq
  calc
    _ ≤ q^t*(9*((planarCells R id q).card:ℝ)) := mul_le_mul_of_nonneg_left hc (Real.rpow_pos_of_pos hq t).le
    _ = 9*(q^t*((planarCells R id q).card:ℝ)) := by ring
    _ ≤ 9*(2304*(100*K)^2) := mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by ring
/-- At the literal scale of a cover-AD law, the FULL original occupied grid
 has a linear K bound. This consumes the scheduled union-Y hypothesis. -/
theorem original_literal_own_scale_grid_mass (Y : Finset (ℝ × ℝ))
    {q K t : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hK : 0 ≤ K)
    (hbox : ∀ g ∈ Y, ‖g‖ ≤ 1) (H : LiteralCoverAD Y q K t) :
    q^t*((planarCells Y id q).card:ℝ) ≤ 25*K := by
  have hboxFn : ∀ p ∈ Y.image toPair.symm, ∀ i : Fin 2, |p i| ≤ 1 := by
    intro p hp i
    obtain ⟨g,hg,rfl⟩ := mem_image.mp hp
    have hh := max_le_iff.mp (hbox g hg)
    fin_cases i
    · change |g.1| ≤ 1
      exact hh.1
    · change |g.2| ≤ 1
      exact hh.2
  obtain ⟨R,hRY,himage,hinj⟩ := NativeCoverADRepresentatives.exists_original_representatives
    (Y.image toPair.symm) (ADGridCoverMenus.gridLabel q)
  have hc := NativeCoverADRepresentatives.representative_total_upper hq hq1 hK hboxFn H hRY hinj
  have hcard : (planarCells Y id q).card=R.card := by
    have hh := pair_grid_card (Y.image toPair.symm) q
    rw [pair_image_readback,←himage,card_image_of_injOn hinj] at hh
    exact hh
  rw [hcard]
  have hpow : 0 < q^t := Real.rpow_pos_of_pos hq t
  have hh := mul_le_mul_of_nonneg_left hc hpow.le
  have hid : q^t*(25*K*(1/q)^t)=25*K := by
    rw [Real.div_rpow (by norm_num : (0:ℝ)≤1) hq.le,Real.one_rpow]
    field_simp
  exact hh.trans_eq hid
end OriginalLiteralGrainProfiles
