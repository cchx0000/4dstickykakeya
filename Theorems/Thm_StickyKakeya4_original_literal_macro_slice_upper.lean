import Theorems.Thm_StickyKakeya4_original_literal_macro_density
import Theorems.Thm_StickyKakeya4_original_tube_slice_occupancy
import Theorems.Thm_StickyKakeya4_spine_column_counting
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3500000
noncomputable section
namespace OriginalLiteralMacroSliceUpper
open Classical Finset NativeTangentGridCoarsening OriginalWGrainDrift OriginalPhaseCellPopulation
open OriginalMacroGrainReadback OriginalLiteralGrainProfiles OriginalRepresentativeGridComparison
private lemma ecover_readback (Y : Finset (Fin 2 → ℝ)) (delta : ℝ) (a : Fin 2 → ℝ) (r : ℝ) :
    NativeEuclideanCoverInput.ecover Y delta a r=
      (((NativeEuclideanCoverInput.eball Y a r).image (ADGridCoverMenus.gridLabel delta)).card:ℝ) := by
  unfold NativeEuclideanCoverInput.ecover
  apply congrArg (fun S : Finset (Fin 2 → ℤ) => (S.card:ℝ))
  ext k
  simp only [mem_image]
/-- A literal subset of an original planar grain ball is counted by the
 original Euclidean fine-cover law, with the explicit sup-to-Euclidean factor. -/
theorem original_grain_ball_grid_upper (Y S : Finset (ℝ × ℝ)) (a : ℝ × ℝ)
    {delta K t R : ℝ} (hR : 0 ≤ R) (hdR : delta ≤ 2*R) (hR1 : 2*R ≤ 1)
    (hSY : S ⊆ Y) (ha : a ∈ Y) (hnear : ∀ g ∈ S, ‖g-a‖ ≤ R)
    (H : LiteralCoverAD Y delta K t) :
    ((planarCells S id delta).card:ℝ) ≤ K*(2*R/delta)^t := by
  let SF := S.image toPair.symm
  let YF := Y.image toPair.symm
  have hs : SF ⊆ NativeEuclideanCoverInput.eball YF (toPair.symm a) (2*R) := by
    intro f hf
    obtain ⟨g,hg,rfl⟩ := mem_image.mp hf
    refine mem_filter.mpr ⟨mem_image_of_mem _ (hSY hg),?_⟩
    have hn := max_le_iff.mp (hnear g hg)
    have hd := EuclideanAlignmentPatches.euclidean_dist_le_card_mul
      (toPair.symm g) (toPair.symm a) R hR (fun i => by
        fin_cases i
        · change |g.1-a.1| ≤ R
          exact hn.1
        · change |g.2-a.2| ≤ R
          exact hn.2)
    simpa only [Nat.cast_ofNat] using hd
  have hcard := pair_grid_card SF delta
  rw [pair_image_readback] at hcard
  have hc : (((SF.image (ADGridCoverMenus.gridLabel delta)).card):ℝ) ≤
      NativeEuclideanCoverInput.ecover YF delta (toPair.symm a) (2*R) := by
    rw [ecover_readback]
    exact_mod_cast card_le_card (image_subset_image hs (f := ADGridCoverMenus.gridLabel delta))
  rw [hcard]
  exact hc.trans (H (toPair.symm a) (mem_image_of_mem _ ha) (2*R) hdR hR1).2
variable {P : Type*}
private lemma same_macro_x_close (height x : P → ℝ) (y : P → ℝ × ℝ) {q : ℝ} (hq : 0 < q)
    {p p0 : P} (hcell : physicalCell q height x y p=physicalCell q height x y p0) : |x p-x p0| ≤ q := by
  have he : ⌊x p/q⌋=⌊x p0/q⌋ := by
    simpa only [physicalCell] using congrArg (fun k : ℤ × (ℤ × (ℤ × ℤ)) => k.2.1) hcell
  exact (SpineColumnCounting.same_floor_scaled_close hq he).le
private lemma same_macro_y_close (height x : P → ℝ) (y : P → ℝ × ℝ) {q : ℝ} (hq : 0 < q)
    {p p0 : P} (hcell : physicalCell q height x y p=physicalCell q height x y p0) : ‖y p-y p0‖ ≤ q := by
  have h1 : ⌊(y p).1/q⌋=⌊(y p0).1/q⌋ := by
    simpa only [physicalCell] using congrArg (fun k : ℤ × (ℤ × (ℤ × ℤ)) => k.2.2.1) hcell
  have h2 : ⌊(y p).2/q⌋=⌊(y p0).2/q⌋ := by
    simpa only [physicalCell] using congrArg (fun k : ℤ × (ℤ × (ℤ × ℤ)) => k.2.2.2) hcell
  exact max_le (SpineColumnCounting.same_floor_scaled_close hq h1).le
    (SpineColumnCounting.same_floor_scaled_close hq h2).le
/-- At one original height, the grain image in a literal physical q-cell
 lies in an original grain ball. The fine-cover law supplies its population. -/
theorem original_macro_grain_grid_upper (E S : Finset P) (hSE : S ⊆ E)
    (height x : P → ℝ) (y : P → ℝ × ℝ) (F : ℝ → ℝ →L[ℝ] ℝ × ℝ)
    (z : ℝ) (k : ℤ × (ℤ × (ℤ × ℤ))) {delta q K t : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : 4*q ≤ 1) (hK : 0 ≤ K) (ht2 : t ≤ 2)
    (hheight : ∀ p ∈ S, height p=z) (hcell : ∀ p ∈ S, physicalCell q height x y p=k)
    (hF : ‖F z‖ ≤ 1)
    (H : LiteralCoverAD (grains E height (grainCoordinate height x y F) z) delta K t) :
    ((planarCells S (grainCoordinate height x y F) delta).card:ℝ) ≤ 16*K*(q/delta)^t := by
  have hq : 0 < q := hd.trans_le hdq
  by_cases hS : S.Nonempty
  · obtain ⟨p0,hp0⟩ := hS
    let grain := grainCoordinate height x y F
    let Y := grains E height grain z
    have hpY : grain p0 ∈ Y := mem_image_of_mem _ (mem_filter.mpr ⟨hSE hp0,hheight p0 hp0⟩)
    have hSY : S.image grain ⊆ Y := by
      intro g hg
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hg
      exact mem_image_of_mem _ (mem_filter.mpr ⟨hSE hp,hheight p hp⟩)
    have hnear : ∀ g ∈ S.image grain, ‖g-grain p0‖ ≤ 2*q := by
      intro g hg
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hg
      have heq := (hcell p hp).trans (hcell p0 hp0).symm
      have hx := same_macro_x_close height x y hq heq
      have hy := same_macro_y_close height x y hq heq
      have hf : ‖F z (x p-x p0)‖ ≤ q :=
        ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hF hx (norm_nonneg _) (by norm_num))).trans_eq (one_mul _)
      have hid : grain p-grain p0=(y p-y p0)-F z (x p-x p0) := by
        dsimp [grain,grainCoordinate]
        rw [hheight p hp,hheight p0 hp0,map_sub]
        abel
      rw [hid]
      exact (norm_sub_le _ _).trans (by linarith only [hy,hf])
    have hc := original_grain_ball_grid_upper Y (S.image grain) (grain p0)
      (show 0 ≤ 2*q by positivity) (show delta ≤ 2*(2*q) by linarith) (by linarith) hSY hpY hnear H
    have heq : planarCells (S.image grain) id delta=planarCells S grain delta := by
      ext a
      simp only [planarCells,mem_image,id_eq]
      constructor
      · rintro ⟨g,⟨p,hp,rfl⟩,ha⟩
        exact ⟨p,hp,ha⟩
      · rintro ⟨p,hp,ha⟩
        exact ⟨grain p,⟨p,hp,rfl⟩,ha⟩
    rw [heq,show 2*(2*q)/delta=4*(q/delta) by ring,
      Real.mul_rpow (by norm_num : (0:ℝ)≤4) (by positivity : 0 ≤ q/delta)] at hc
    have hfour : (4:ℝ)^t ≤ 16 := by
      have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤4) ht2
      norm_num at hh
      exact hh
    have hh := mul_le_mul_of_nonneg_right hfour (show 0 ≤ K*(q/delta)^t by positivity)
    exact hc.trans (by nlinarith only [hh])
  · rw [not_nonempty_iff_eq_empty.mp hS]
    simp only [planarCells,image_empty,card_empty,Nat.cast_zero]
    positivity
private lemma grain_center_bound {delta : ℝ} (hd : 0 < delta) (v : ℝ × ℝ) (k : ℤ × ℤ)
    (hk : (⌊v.1/delta⌋,⌊v.2/delta⌋)=k) :
    ‖v-(delta*((k.1:ℝ)+1/2),delta*((k.2:ℝ)+1/2))‖ ≤ delta/2 := by
  have h1 : ⌊(v.1-0)/delta⌋=k.1 := by simpa using congrArg Prod.fst hk
  have h2 : ⌊(v.2-0)/delta⌋=k.2 := by simpa using congrArg Prod.snd hk
  have hp1 := coarse_floor_interval hd h1
  have hp2 := coarse_floor_interval hd h2
  change max |v.1-delta*((k.1:ℝ)+1/2)| |v.2-delta*((k.2:ℝ)+1/2)| ≤ delta/2
  apply max_le_iff.mpr
  exact ⟨abs_le.mpr ⟨by nlinarith only [hp1.1,hp1.2],by nlinarith only [hp1.1,hp1.2]⟩,
    abs_le.mpr ⟨by nlinarith only [hp2.1,hp2.2],by nlinarith only [hp2.1,hp2.2]⟩⟩
/-- The upper population of an actual original height slice in a macro-cell
 follows from original E separation and literal fine Y cover AD. It is not
 an input height-fiber cap. -/
theorem original_macro_height_point_upper (E S : Finset P) (hSE : S ⊆ E)
    (height x : P → ℝ) (y : P → ℝ × ℝ) (F : ℝ → ℝ →L[ℝ] ℝ × ℝ)
    (z : ℝ) (k : ℤ × (ℤ × (ℤ × ℤ))) {delta q K t : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : 4*q ≤ 1) (hK : 0 ≤ K) (ht2 : t ≤ 2)
    (hsep : ∀ p ∈ E, ∀ p0 ∈ E, p ≠ p0 → delta ≤
      dist (OriginalTubeSliceOccupancy.embedding height x y p) (OriginalTubeSliceOccupancy.embedding height x y p0))
    (hheight : ∀ p ∈ S, height p=z) (hcell : ∀ p ∈ S, physicalCell q height x y p=k)
    (hF : ‖F z‖ ≤ 1)
    (H : LiteralCoverAD (grains E height (grainCoordinate height x y F) z) delta K t) :
    (S.card:ℝ) ≤ 155520*K*(q/delta)^(t+1) := by
  have hq : 0 < q := hd.trans_le hdq
  let grain := grainCoordinate height x y F
  let index : P → ℤ × (ℤ × ℤ) := fun p =>
    (⌊x p/delta⌋,(⌊(grain p).1/delta⌋,⌊(grain p).2/delta⌋))
  have hinj := OriginalTubeSliceOccupancy.physical_cell_injective E height x y hd hsep
  have hfiber : ∀ j ∈ S.image index,
      (((S.filter (fun p => index p=j)).image id).card:ℝ) ≤ 3240 := by
    intro j _hj
    let Q := S.filter (fun p => index p=j)
    have hcard : (physicalCells Q (delta/8) height x y).card=Q.card := by
      apply card_image_iff.mpr
      intro p hp p0 hp0 heq
      exact hinj (hSE (mem_filter.mp hp).1) (hSE (mem_filter.mp hp0).1) heq
    have hgeom := OriginalWindowPhysicalCells.same_x_window_physical_cells Q height x y F z 0
      (delta*((j.2.1:ℝ)+1/2),delta*((j.2.2:ℝ)+1/2)) j.1 hd
      (by positivity : 0 < delta/8) (by positivity : 0 ≤ delta/2) (by norm_num : (0:ℝ)≤1)
      (fun p hp => hheight p (mem_filter.mp hp).1) hF
      (fun p hp => by simpa [index] using congrArg Prod.fst (mem_filter.mp hp).2)
      (fun p hp => grain_center_bound hd _ _ (congrArg Prod.snd (mem_filter.mp hp).2))
    have hc : (delta/(delta/8)+2)*((2*(delta/2)+1*delta)/(delta/8)+2)^2=(3240:ℝ) := by
      have h1 : delta/(delta/8)=(8:ℝ) := by field_simp
      have h2 : (2*(delta/2)+1*delta)/(delta/8)=(16:ℝ) := by field_simp; norm_num
      rw [h1,h2]
      norm_num
    rw [hcard,hc] at hgeom
    simpa only [image_id] using hgeom
  have hpoints := image_card_le_real_mul_of_fiber_images S id index 3240 hfiber
  rw [image_id] at hpoints
  have hX : ((scalarCells S x delta).card:ℝ) ≤ 3*(q/delta) := by
    have hh := scalar_interval_grid_card S x (c := q*(k.2.1:ℝ)) hd hq.le (fun p hp => by
      have hfloor : ⌊(x p-0)/q⌋=k.2.1 := by
        simpa [physicalCell] using congrArg (fun j : ℤ × (ℤ × (ℤ × ℤ)) => j.2.1) (hcell p hp)
      have hb := coarse_floor_interval hq hfloor
      exact ⟨by linarith only [hb.1],by linarith only [hb.2]⟩)
    have hratio : 1 ≤ q/delta := (le_div_iff₀ hd).mpr (by simpa using hdq)
    exact hh.trans (by linarith only [hratio])
  have hG := original_macro_grain_grid_upper E S hSE height x y F z k hd hdq hq1 hK ht2 hheight hcell hF H
  have hsub : S.image index ⊆ scalarCells S x delta ×ˢ planarCells S grain delta := by
    intro j hj
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hj
    exact mem_product.mpr ⟨mem_image_of_mem _ hp,mem_image_of_mem _ hp⟩
  have hindex : ((S.image index).card:ℝ) ≤
      ((scalarCells S x delta).card:ℝ)*((planarCells S grain delta).card:ℝ) := by
    have hh := card_le_card hsub
    rw [card_product] at hh
    exact_mod_cast hh
  calc
    _ ≤ 3240*((S.image index).card:ℝ) := hpoints
    _ ≤ 3240*(((scalarCells S x delta).card:ℝ)*((planarCells S grain delta).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hindex (by norm_num)
    _ ≤ 3240*((3*(q/delta))*(16*K*(q/delta)^t)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul hX hG (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [Real.rpow_add (div_pos hq hd),Real.rpow_one]; ring
end OriginalLiteralMacroSliceUpper
