import Theorems.Thm_StickyKakeya4_native_scalar_cover_ad
import Theorems.Thm_StickyKakeya4_original_separated_height_cap
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
noncomputable section
namespace OriginalScalarLiteralCoverCount
open Classical Finset NativeScalarCoverAD FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open scoped BigOperators
/-- The literal cover is the actual occupied image; the extensional
 readback also fixes the finite set decision-instance presentation. -/
lemma cover_count_readback (Phi : Finset ℝ) (delta a r : ℝ) :
    coverCount Phi delta a r=(((carrierBall Phi a r).image (cell delta)).card:ℝ) := by
  unfold coverCount
  apply congrArg (fun S : Finset ℤ => (S.card:ℝ))
  ext k
  simp only [mem_image]
/-- A small ORIGINAL subset is charged to the literal cover law, without
 assuming a point-count law or separation of the original scalar set. -/
theorem diameter_grid_upper (Phi S : Finset ℝ) {delta K kappa : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hK : 0 ≤ K)
    (H : CoverADBounds Phi delta K kappa) (hS : S ⊆ Phi)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1) :
    ((S.image (cell delta)).card:ℝ) ≤ K*(1/delta)^kappa := by
  by_cases hne : S.Nonempty
  · obtain ⟨a,ha⟩ := hne
    have hs : S ⊆ carrierBall Phi a 1 := by
      intro x hx
      exact (mem_carrierBall Phi x a 1).mpr ⟨hS hx,hdiam x hx a ha⟩
    have hc : ((S.image (cell delta)).card:ℝ) ≤ coverCount Phi delta a 1 := by
      rw [cover_count_readback]
      exact_mod_cast card_le_card (image_subset_image hs (f := cell delta))
    exact hc.trans (H a (hS ha) 1 hd1 le_rfl).2
  · rw [not_nonempty_iff_eq_empty.mp hne,image_empty,card_empty,Nat.cast_zero]
    exact mul_nonneg hK (Real.rpow_nonneg (by positivity) _)
/-- The two original half-intervals give a global occupied-cell bound. -/
theorem boxed_cover_grid_upper (Phi : Finset ℝ) {delta K kappa : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hK : 0 ≤ K)
    (H : CoverADBounds Phi delta K kappa) (hbox : ∀ x ∈ Phi, |x| ≤ 1) :
    ((Phi.image (cell delta)).card:ℝ) ≤ 2*K*(1/delta)^kappa := by
  let L := Phi.filter (fun x => x ≤ 0)
  let R := Phi.filter (fun x => ¬x ≤ 0)
  have hL : ((L.image (cell delta)).card:ℝ) ≤ K*(1/delta)^kappa := by
    apply diameter_grid_upper Phi L hd hd1 hK H (filter_subset _ _)
    intro x hx y hy
    obtain ⟨hxP,hx0⟩ := mem_filter.mp hx
    obtain ⟨hyP,hy0⟩ := mem_filter.mp hy
    have hxb := abs_le.mp (hbox x hxP)
    have hyb := abs_le.mp (hbox y hyP)
    rw [Real.dist_eq]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hR : ((R.image (cell delta)).card:ℝ) ≤ K*(1/delta)^kappa := by
    apply diameter_grid_upper Phi R hd hd1 hK H (filter_subset _ _)
    intro x hx y hy
    obtain ⟨hxP,hx0⟩ := mem_filter.mp hx
    obtain ⟨hyP,hy0⟩ := mem_filter.mp hy
    have hxb := abs_le.mp (hbox x hxP)
    have hyb := abs_le.mp (hbox y hyP)
    have hxp := lt_of_not_ge hx0
    have hyp := lt_of_not_ge hy0
    rw [Real.dist_eq]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hu : Phi=L ∪ R := (filter_union_filter_not_eq _ _).symm
  have hc : ((Phi.image (cell delta)).card:ℝ) ≤
      ((L.image (cell delta)).card:ℝ)+((R.image (cell delta)).card:ℝ) := by
    rw [hu,image_union]
    exact_mod_cast card_union_le (L.image (cell delta)) (R.image (cell delta))
  nlinarith only [hc,hL,hR]
/-- Literal cover upper bounds hold at every real center and every radius
 above the mesh; the large-radius case uses the original bounded interval. -/
theorem boxed_cover_allcenter (Phi : Finset ℝ) {delta K kappa : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hK : 0 ≤ K) (hk : 0 ≤ kappa)
    (H : CoverADBounds Phi delta K kappa) (hbox : ∀ x ∈ Phi, |x| ≤ 1)
    (a r : ℝ) (hr : delta ≤ r) :
    coverCount Phi delta a r ≤ 4*K*(2*r/delta)^kappa := by
  have hr0 : 0 < r := hd.trans_le hr
  by_cases hsmall : 2*r ≤ 1
  · by_cases hne : (carrierBall Phi a r).Nonempty
    · obtain ⟨c,hc⟩ := hne
      obtain ⟨hcP,hca⟩ := (mem_carrierBall Phi c a r).mp hc
      have hs : carrierBall Phi a r ⊆ carrierBall Phi c (2*r) := by
        intro x hx
        obtain ⟨hxP,hxa⟩ := (mem_carrierBall Phi x a r).mp hx
        refine (mem_carrierBall Phi x c (2*r)).mpr ⟨hxP,?_⟩
        have hh := dist_triangle x a c
        rw [dist_comm a c] at hh
        linarith only [hh,hxa,hca]
      have hc' : coverCount Phi delta a r ≤ coverCount Phi delta c (2*r) := by
        simp only [cover_count_readback]
        exact_mod_cast card_le_card (image_subset_image hs (f := cell delta))
      have hu := hc'.trans (H c hcP (2*r) (by linarith) hsmall).2
      have hp : 0 ≤ K*(2*r/delta)^kappa := by positivity
      nlinarith only [hu,hp]
    · unfold coverCount
      rw [not_nonempty_iff_eq_empty.mp hne,image_empty,card_empty,Nat.cast_zero]
      positivity
  · have hc : coverCount Phi delta a r ≤ ((Phi.image (cell delta)).card:ℝ) := by
      rw [cover_count_readback]
      exact_mod_cast card_le_card (image_subset_image (filter_subset _ _) (f := cell delta))
    have hp := Real.rpow_le_rpow (by positivity : (0:ℝ)≤1/delta)
      (div_le_div_of_nonneg_right (by linarith : 1 ≤ 2*r) hd.le) hk
    have hb := hc.trans (boxed_cover_grid_upper Phi hd hd1 hK H hbox)
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2*K by positivity)
    have hn : 0 ≤ K*(2*r/delta)^kappa := by positivity
    nlinarith only [hb,hh,hn]
/-- A q-separated original scalar subfamily is controlled by its occupied
 q-cells. No separation of a covering source alphabet is required. -/
theorem separated_card_eq_grid (C : Finset ℝ) {q : ℝ} (hq : 0 < q) (hsep : Separated C q) :
    (C.image (cell q)).card=C.card := by
  apply card_image_of_injOn
  apply OriginalSeparatedHeightCap.floor_injective_of_separated C hq
  intro x hx y hy hxy
  simpa only [Real.dist_eq] using hsep x hx y hy hxy
end OriginalScalarLiteralCoverCount
