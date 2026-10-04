import Theorems.Thm_StickyKakeya4_original_literal_macro_density
import Theorems.Thm_StickyKakeya4_original_literal_height_window
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace OriginalHeightWindowMacroCells
open Classical Finset NativeTangentGridCoarsening OriginalWGrainDrift OriginalPhaseCellPopulation
open OriginalMacroGrainReadback OriginalLiteralGrainProfiles
variable {P : Type*}
/-- The scheduled source union of complete original grain fibers is exactly
 the image of the same original point carrier. -/
theorem actual_union_grain_image (E : Finset P) (height : P → ℝ) (grain : P → ℝ × ℝ) :
    (E.image height).biUnion (grains E height grain)=E.image grain := by
  ext g
  constructor
  · intro hg
    obtain ⟨z,_hz,hgz⟩ := mem_biUnion.mp hg
    obtain ⟨p,hp,hpg⟩ := mem_image.mp hgz
    exact mem_image.mpr ⟨p,(mem_filter.mp hp).1,hpg⟩
  · intro hg
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hg
    exact mem_biUnion.mpr ⟨height p,mem_image_of_mem _ hp,
      mem_image_of_mem _ (mem_filter.mpr ⟨hp,rfl⟩)⟩
/-- For points in fixed original height and x grid cells, only the actual
 transverse physical grid cells remain to be counted. -/
theorem fixed_height_x_cell_count (E : Finset P) (height x : P → ℝ) (y : P → ℝ × ℝ)
    (q : ℝ) (hz hx : ℤ) (hheight : ∀ p ∈ E, ⌊height p/q⌋=hz)
    (hxcell : ∀ p ∈ E, ⌊x p/q⌋=hx) :
    (physicalCells E q height x y).card ≤ (planarCells E y q).card := by
  have hs : physicalCells E q height x y ⊆ {hz} ×ˢ ({hx} ×ˢ planarCells E y q) := by
    intro k hk
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hk
    exact mem_product.mpr ⟨mem_singleton.mpr (hheight p hp),
      mem_product.mpr ⟨mem_singleton.mpr (hxcell p hp),mem_image_of_mem _ hp⟩⟩
  have hh := card_le_card hs
  simpa only [card_product,card_singleton,one_mul] using hh
private lemma grain_center_bound {q : ℝ} (hq : 0 < q) (v : ℝ × ℝ) (k : ℤ × ℤ)
    (hk : (⌊v.1/q⌋,⌊v.2/q⌋)=k) :
    ‖v-(q*((k.1:ℝ)+1/2),q*((k.2:ℝ)+1/2))‖ ≤ q/2 := by
  have h1 : ⌊(v.1-0)/q⌋=k.1 := by simpa using congrArg Prod.fst hk
  have h2 : ⌊(v.2-0)/q⌋=k.2 := by simpa using congrArg Prod.snd hk
  have hp1 := coarse_floor_interval hq h1
  have hp2 := coarse_floor_interval hq h2
  change max |v.1-q*((k.1:ℝ)+1/2)| |v.2-q*((k.2:ℝ)+1/2)| ≤ q/2
  apply max_le_iff.mpr
  exact ⟨abs_le.mpr ⟨by nlinarith only [hp1.1,hp1.2],by nlinarith only [hp1.1,hp1.2]⟩,
    abs_le.mpr ⟨by nlinarith only [hp2.1,hp2.2],by nlinarith only [hp2.1,hp2.2]⟩⟩
/-- The scheduled height-window law controls original physical macro-cells
 using the literal union-Y profile. No macro-cell count is supplied as input. -/
theorem original_window_macro_grid_mass (E : Finset P) (height x : P → ℝ) (y : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (z0 : ℝ) (hz : ℤ) {q L K t : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hheight : ∀ p ∈ E, ⌊height p/q⌋=hz) (hx : ∀ p ∈ E, |x p| ≤ 1)
    (hF : ‖F z0‖ ≤ 1) (hosc : ∀ p ∈ E, ‖F (height p)-F z0‖ ≤ L*q)
    (hYbox : ∀ g ∈ E.image (grainCoordinate height x y F), ‖g‖ ≤ 1)
    (hY : LiteralCoverAD (E.image (grainCoordinate height x y F)) q K t) :
    q^(t+1)*((physicalCells E q height x y).card:ℝ) ≤ 100*K*(2*L+4)^2 := by
  let grain := grainCoordinate height x y F
  let index : P → ℤ × (ℤ × ℤ) := fun p => (⌊x p/q⌋,(⌊(grain p).1/q⌋,⌊(grain p).2/q⌋))
  have hfiber : ∀ k ∈ E.image index,
      (((E.filter (fun p => index p=k)).image (physicalCell q height x y)).card:ℝ) ≤ (2*L+4)^2 := by
    intro k _hk
    let S := E.filter (fun p => index p=k)
    let mid : ℝ := q*((k.1:ℝ)+1/2)
    let gmid : ℝ × ℝ := (q*((k.2.1:ℝ)+1/2),q*((k.2.2:ℝ)+1/2))
    let center := gmid+F z0 mid
    have hnear : ∀ p ∈ S, ‖y p-center‖ ≤ (L+1)*q := by
      intro p hp
      have hpE := (mem_filter.mp hp).1
      have hidx := (mem_filter.mp hp).2
      have hg : ‖grain p-gmid‖ ≤ q/2 := grain_center_bound hq _ _ (congrArg Prod.snd hidx)
      have hxcell : ⌊(x p-0)/q⌋=k.1 := by simpa [index] using congrArg Prod.fst hidx
      have hb := coarse_floor_interval hq hxcell
      have hxm : |x p-mid| ≤ q/2 := by
        dsimp [mid]
        exact abs_le.mpr ⟨by nlinarith only [hb.1,hb.2],by nlinarith only [hb.1,hb.2]⟩
      have hvar : ‖(F (height p)-F z0) (x p)‖ ≤ L*q := by
        have hh := (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (hosc p hpE) (hx p hpE) (norm_nonneg _) (mul_nonneg hL hq.le))
        simpa only [mul_one] using hh
      have hbase : ‖F z0 (x p-mid)‖ ≤ q/2 := by
        have hh := (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul hF hxm (norm_nonneg _) (by norm_num))
        simpa only [one_mul] using hh
      have hid : y p-center=(grain p-gmid)+(F (height p)-F z0) (x p)+F z0 (x p-mid) := by
        dsimp [grain,grainCoordinate,center]
        rw [map_sub,sub_apply]
        abel
      rw [hid]
      calc
        _ ≤ ‖(grain p-gmid)+(F (height p)-F z0) (x p)‖+‖F z0 (x p-mid)‖ := norm_add_le _ _
        _ ≤ (‖grain p-gmid‖+‖(F (height p)-F z0) (x p)‖)+‖F z0 (x p-mid)‖ :=
          add_le_add (norm_add_le _ _) (le_refl _)
        _ ≤ _ := by linarith only [hg,hvar,hbase]
    have hgrid := planar_centered_grid_card S y center hq (show 0 ≤ L+1 by positivity)
      (fun p hp => by
        have hh := max_le_iff.mp (hnear p hp)
        simpa only [Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs] using hh)
    have hphys : ((physicalCells S q height x y).card:ℝ) ≤ (planarCells S y q).card := by
      exact_mod_cast fixed_height_x_cell_count S height x y q hz k.1
        (fun p hp => hheight p (mem_filter.mp hp).1)
        (fun p hp => congrArg Prod.fst (mem_filter.mp hp).2)
    have hh := hphys.trans hgrid
    have hleft : S.image (physicalCell q height x y)=physicalCells S q height x y := by
      ext c
      simp only [physicalCells,mem_image]
    change ((S.image (physicalCell q height x y)).card:ℝ) ≤ (2*L+4)^2
    rw [hleft]
    simpa only [show (2*(L+1)+2)^2=(2*L+4)^2 by ring] using hh
  have hphys := image_card_le_real_mul_of_fiber_images E (physicalCell q height x y) index ((2*L+4)^2) hfiber
  have hX : ((scalarCells E x q).card:ℝ) ≤ 4/q := by
    have hh := scalar_interval_grid_card E x (c := -1) hq (by norm_num : (0:ℝ)≤2)
      (fun p hp => ⟨(abs_le.mp (hx p hp)).1,by linarith [(abs_le.mp (hx p hp)).2]⟩)
    have hi : 1 ≤ 1/q := (le_div_iff₀ hq).mpr (by simpa using hq1)
    apply hh.trans
    rw [show 2/q=2*(1/q) by ring,show 4/q=4*(1/q) by ring]
    linarith only [hi]
  have hsub : E.image index ⊆ scalarCells E x q ×ˢ planarCells E grain q := by
    intro k hk
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hk
    exact mem_product.mpr ⟨mem_image_of_mem _ hp,mem_image_of_mem _ hp⟩
  have hindex : ((E.image index).card:ℝ) ≤ (4/q)*((planarCells E grain q).card:ℝ) := by
    have hh : ((E.image index).card:ℝ) ≤ ((scalarCells E x q).card:ℝ)*((planarCells E grain q).card:ℝ) := by
      have hh := card_le_card hsub
      rw [card_product] at hh
      exact_mod_cast hh
    exact hh.trans (mul_le_mul_of_nonneg_right hX (Nat.cast_nonneg _))
  have hgrideq : planarCells (E.image grain) id q=planarCells E grain q := by
    ext k
    simp only [planarCells,mem_image,id_eq]
    constructor
    · rintro ⟨g,⟨p,hp,rfl⟩,hk⟩
      exact ⟨p,hp,hk⟩
    · rintro ⟨p,hp,hk⟩
      exact ⟨grain p,⟨p,hp,rfl⟩,hk⟩
  have hgrain := original_literal_own_scale_grid_mass (E.image grain) hq hq1 hK hYbox hY
  rw [hgrideq] at hgrain
  have hmul := mul_le_mul_of_nonneg_left
    (hphys.trans (mul_le_mul_of_nonneg_left hindex (sq_nonneg _))) (Real.rpow_pos_of_pos hq (t+1)).le
  have hid : q^(t+1)*((2*L+4)^2*((4/q)*((planarCells E grain q).card:ℝ)))=
      4*(2*L+4)^2*(q^t*((planarCells E grain q).card:ℝ)) := by
    rw [Real.rpow_add hq,Real.rpow_one]
    field_simp
  rw [hid] at hmul
  exact hmul.trans (by nlinarith only [mul_le_mul_of_nonneg_left hgrain (show 0 ≤ 4*(2*L+4)^2 by positivity)])
end OriginalHeightWindowMacroCells
