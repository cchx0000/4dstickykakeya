import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening
import Theorems.Thm_StickyKakeya4_finite_voronoi_real_ad_coarsening
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalPlanarADGridPopulation
open Classical Finset FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening NativeTangentGridCoarsening
abbrev Plane := ℝ × ℝ
def cell (mesh : ℝ) (p : Plane) : ℤ × ℤ := (⌊p.1/mesh⌋,⌊p.2/mesh⌋)
private lemma planar_cells_eq (Y : Finset Plane) (q : ℝ) : planarCells Y id q=Y.image (cell q) := by
  ext k
  simp only [planarCells,cell,mem_image,id_eq]
private lemma same_unit_cell_dist (p c : Plane) (heq : cell 1 p=cell 1 c) : dist p c ≤ 1 := by
  have h1 : ⌊p.1/(1:ℝ)⌋=⌊c.1/(1:ℝ)⌋ := congrArg Prod.fst heq
  have h2 : ⌊p.2/(1:ℝ)⌋=⌊c.2/(1:ℝ)⌋ := congrArg Prod.snd heq
  have hp1 := coarse_floor_interval (by norm_num : (0:ℝ)<1) h1
  have hc1 := coarse_floor_interval (by norm_num : (0:ℝ)<1) (rfl : ⌊c.1/(1:ℝ)⌋=⌊c.1/(1:ℝ)⌋)
  have hp2 := coarse_floor_interval (by norm_num : (0:ℝ)<1) h2
  have hc2 := coarse_floor_interval (by norm_num : (0:ℝ)<1) (rfl : ⌊c.2/(1:ℝ)⌋=⌊c.2/(1:ℝ)⌋)
  rw [dist_eq_norm]
  change max |p.1-c.1| |p.2-c.2| ≤ 1
  apply max_le_iff.mpr
  constructor
  · exact abs_le.mpr ⟨by linarith only [hp1.1,hp1.2,hc1.1,hc1.2],by linarith only [hp1.1,hp1.2,hc1.1,hc1.2]⟩
  · exact abs_le.mpr ⟨by linarith only [hp2.1,hp2.2,hc2.1,hc2.2],by linarith only [hp2.1,hp2.2,hc2.1,hc2.2]⟩
/-- Original AD in the actual unit box gives total fine mass; sixteen
 literal unit-grid cells remove the diameter-two versus radius-one mismatch. -/
theorem original_planar_total_mass (Y : Finset Plane) {delta K t : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hK : 0 < K)
    (hbox : ∀ y ∈ Y, ‖y‖ ≤ 1) (hAD : ADBounds Y delta K t) :
    delta^t*(Y.card:ℝ) ≤ 16*K := by
  have hp : 0 < delta^t := Real.rpow_pos_of_pos hd t
  have had := scaled_bounds_of_ADBounds hd hK hAD
  have hf : ∀ k ∈ Y.image (cell 1), (((Y.filter (fun p => cell 1 p=k)).image id).card:ℝ) ≤ K/(delta^t) := by
    intro k hk
    obtain ⟨c,hc,hck⟩ := mem_image.mp hk
    have hsub : Y.filter (fun p => cell 1 p=k) ⊆ carrierBall Y c 1 := by
      intro p hpp
      obtain ⟨hpY,hpk⟩ := mem_filter.mp hpp
      exact (mem_carrierBall Y p c 1).mpr ⟨hpY,same_unit_cell_dist p c (hpk.trans hck.symm)⟩
    have hcard : ((Y.filter (fun p => cell 1 p=k)).card:ℝ) ≤ (carrierBall Y c 1).card := by
      exact_mod_cast card_le_card hsub
    have hu := (had c hc 1 hd1 le_rfl).2
    rw [Real.one_rpow,mul_one] at hu
    have hh : ((Y.filter (fun p => cell 1 p=k)).card:ℝ) ≤ K/(delta^t) :=
      (le_div_iff₀ hp).mpr (by nlinarith only [mul_le_mul_of_nonneg_left hcard hp.le,hu])
    simpa only [image_id] using hh
  have hc := image_card_le_real_mul_of_fiber_images Y id (cell 1) (K/(delta^t)) hf
  rw [image_id] at hc
  have hgrid : ((Y.image (cell 1)).card:ℝ) ≤ 16 := by
    have hh := planar_centered_grid_card Y id (0:Plane) (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)≤1)
      (fun p hpY => by
        have hn := max_le_iff.mp (hbox p hpY)
        simpa using hn)
    rw [planar_cells_eq] at hh
    simpa only [show (2*(1:ℝ)+2)^2=16 by norm_num] using hh
  have htotal : (Y.card:ℝ) ≤ (K/(delta^t))*16 := hc.trans
    (mul_le_mul_of_nonneg_left hgrid (div_nonneg hK.le hp.le))
  have hm := mul_le_mul_of_nonneg_left htotal hp.le
  have hid : delta^t*((K/(delta^t))*16)=16*K := by field_simp
  exact hm.trans_eq hid
/-- The literal coarse grid image inherits a covering population bound
 directly from the original fine AD law. It is not an assumed coarse AD set. -/
theorem original_planar_grid_mass (Y : Finset Plane) (hY : Y.Nonempty)
    {delta q K t : ℝ} (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hbox : ∀ y ∈ Y, ‖y‖ ≤ 1) (hAD : ADBounds Y delta K t) :
    q^t*((planarCells Y id q).card:ℝ) ≤ 2304*K^2 := by
  have hq : 0 < q := hd.trans_le hdq
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  obtain ⟨C,hCY,hsep,hcover⟩ := exists_separated_net Y hq
  have hC : C.Nonempty := by
    obtain ⟨p,hp⟩ := hY
    obtain ⟨c,hc,_⟩ := hcover p hp
    exact ⟨c,hc⟩
  have hscaled := scaled_bounds_of_ADBounds hd hK0 hAD
  have hpop := fun (c : Plane) (hc : c ∈ C) => cluster_scaled_population_bounds Y C hC hd hdq hq1 hK ht hCY hsep hcover hscaled (c := c) hc
  have hnet := (subfamily_scaled_population_bounds Y C C hC (subset_refl _) hpop).1
  rw [sum_cluster_card_real] at hnet
  have htotal := original_planar_total_mass Y hd (hdq.trans hq1) hK0 hbox hAD
  have hthree : (3:ℝ)^t ≤ 9 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3) ht2
    norm_num at hh
    exact hh
  have hnetcap : (C.card:ℝ)*q^t ≤ 144*K^2 := by
    calc
      _ ≤ (3:ℝ)^t*K*(delta^t*(Y.card:ℝ)) := by nlinarith only [hnet]
      _ ≤ (3:ℝ)^t*K*(16*K) := mul_le_mul_of_nonneg_left htotal (by positivity)
      _ ≤ 9*K*(16*K) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hthree hK0.le) (by positivity)
      _ = _ := by ring
  have hf : ∀ c ∈ Y.image (owner C hC),
      (((Y.filter (fun p => owner C hC p=c)).image (cell q)).card:ℝ) ≤ 16 := by
    intro c _hc
    have hh := planar_centered_grid_card (Y.filter (fun p => owner C hC p=c)) id c hq (by norm_num : (0:ℝ)≤1)
      (fun p hp => by
        obtain ⟨hpY,hpc⟩ := mem_filter.mp hp
        have hn := (owner_dist_lt Y C hC hcover hpY).le
        rw [hpc,dist_eq_norm] at hn
        simpa only [one_mul,Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs,id_eq] using max_le_iff.mp hn)
    rw [planar_cells_eq] at hh
    simpa only [show (2*(1:ℝ)+2)^2=16 by norm_num] using hh
  have hg := image_card_le_real_mul_of_fiber_images Y (cell q) (owner C hC) 16 hf
  have howners : ((Y.image (owner C hC)).card:ℝ) ≤ C.card := by
    exact_mod_cast card_le_card (show Y.image (owner C hC) ⊆ C from by
      intro c hc
      obtain ⟨p,_hp,rfl⟩ := mem_image.mp hc
      exact owner_mem C hC p)
  have hgrid : ((planarCells Y id q).card:ℝ) ≤ 16*(C.card:ℝ) := by
    rw [planar_cells_eq]
    exact hg.trans (mul_le_mul_of_nonneg_left howners (by norm_num))
  calc
    _ ≤ q^t*(16*(C.card:ℝ)) := mul_le_mul_of_nonneg_left hgrid (Real.rpow_pos_of_pos hq t).le
    _ = 16*((C.card:ℝ)*q^t) := by ring
    _ ≤ 16*(144*K^2) := mul_le_mul_of_nonneg_left hnetcap (by norm_num)
    _ = _ := by ring
end OriginalPlanarADGridPopulation
