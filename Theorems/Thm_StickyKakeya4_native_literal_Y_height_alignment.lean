/- UNVERIFIED source attachment for planar alignment on literal coarse-Y keys.
The input AD bounds are to be supplied by the same-T window/key reader. -/
import Theorems.Thm_StickyKakeya4_native_planar_lemma53
import Theorems.Thm_StickyKakeya4_native_quotient_grid_centers
import Theorems.Thm_StickyKakeya4_native_alignment_tau_range
import Theorems.Thm_StickyKakeya4_native_Y_variable_common_scale_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeLiteralYHeightAlignment
open Classical Finset NativePlanarLemma53 NativeLiteralAlignedSet
open NativeDyadicTubeStopping NativeOriginalAlignmentGeometry NativeQuotientGridCenters
open FiniteVoronoiRealADCoarsening NativeAlignmentTauRange NativeAngularChartSelection
open NormalizedQuantizedPatches

abbrev Key := ℤ × (Fin 2 → ℤ)

def heightKeys (Y : Finset Key) (h : ℤ) : Finset Key := Y.filter (fun z => z.1=h)

def heightPoints (Y : Finset Key) (delta : ℝ) (h : ℤ) : Finset Plane :=
  (heightKeys Y h).image (fun z => center delta z.2)

/-- Exact source-image readback. This is the same literal height slice
as the window reader, in the same Pi sup metric. -/
lemma heightPoints_image_keys {Ω : Type*} (T : Finset Ω) (key : Ω → Key)
    (delta : ℝ) (h : ℤ) :
    heightPoints (T.image key) delta h=
      (T.filter (fun z => (key z).1=h)).image (fun z => center delta (key z).2) := by
  ext x
  simp only [heightPoints,heightKeys,mem_image,mem_filter]
  constructor
  · rintro ⟨y,⟨⟨z,hz,rfl⟩,hheight⟩,he⟩
    exact ⟨z,⟨hz,hheight⟩,he⟩
  · rintro ⟨z,⟨hz,hheight⟩,he⟩
    exact ⟨key z,⟨⟨z,hz,rfl⟩,hheight⟩,he⟩

/-- The actual planar conclusion together with bounded dyadic indices.
This is constructed by Lemma 5.3 below, rather than assumed of the source. -/
structure HeightAlignment (Y : Finset Key) (u : ℕ) (t zeta chi : ℝ) (h : ℤ) where
  rhoDepth : Fin (u+10)
  tauDepth : Fin (u+10)
  exponent : ℝ
  chart : Fin 2
  selected : Finset Plane
  subset : selected ⊆ heightPoints Y ((2:ℝ)⁻¹^u/512) h
  nonempty : selected.Nonempty
  scale_lower : (2:ℝ)⁻¹^u/512 ≤ scale ((2:ℝ)⁻¹^u/512) rhoDepth.val
  scale_order : scale ((2:ℝ)⁻¹^u/512) rhoDepth.val < scale ((2:ℝ)⁻¹^u/512) tauDepth.val
  scale_upper : scale ((2:ℝ)⁻¹^u/512) tauDepth.val ≤ 1
  exponent_nonneg : 0 ≤ exponent
  exponent_upper : exponent ≤ min t 1
  gap : (((2:ℝ)⁻¹^u/512)^(-chi)) ≤
    scale ((2:ℝ)⁻¹^u/512) tauDepth.val / scale ((2:ℝ)⁻¹^u/512) rhoDepth.val
  retention : (scale ((2:ℝ)⁻¹^u/512) rhoDepth.val /
      scale ((2:ℝ)⁻¹^u/512) tauDepth.val)^zeta *
      ((heightPoints Y ((2:ℝ)⁻¹^u/512) h).card:ℝ) ≤ (selected.card:ℝ)
  aligned : ∀a∈selected,NearlyLiteralAligned
    ((NativePaperAlignmentScales.localBall selected a (scale ((2:ℝ)⁻¹^u/512) tauDepth.val)).image
      (NativePaperAlignmentScales.normalization chart a (scale ((2:ℝ)⁻¹^u/512) tauDepth.val)))
    (scale ((2:ℝ)⁻¹^u/512) rhoDepth.val / scale ((2:ℝ)⁻¹^u/512) tauDepth.val)
    t exponent ((scale ((2:ℝ)⁻¹^u/512) rhoDepth.val /
      scale ((2:ℝ)⁻¹^u/512) tauDepth.val)^(-zeta))

lemma heightPoints_nonempty (Y : Finset Key) (delta : ℝ) (h : ℤ)
    (hh : h∈Y.image Prod.fst) : (heightPoints Y delta h).Nonempty := by
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hh
  exact ⟨center delta z.2,mem_image_of_mem _ (mem_filter.mpr ⟨hz,rfl⟩)⟩

lemma heightPoints_card (Y : Finset Key) {delta : ℝ} (hd : 0 < delta) (h : ℤ) :
    (heightPoints Y delta h).card=(heightKeys Y h).card := by
  apply card_image_iff.mpr
  intro x hx y hy he
  exact Prod.ext ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
    (center_injective hd he)

lemma bounded_depth (u j : ℕ) (htop : scale ((2:ℝ)⁻¹^u/512) j ≤ 1) : j < u+10 := by
  have hprod : scale ((2:ℝ)⁻¹^u/512) j*(2:ℝ)^(u+9)=(2:ℝ)^j := by
    calc
      _ = (((2:ℝ)⁻¹^u/512)*(2:ℝ)^(u+9))*(2:ℝ)^j := by unfold scale; ring
      _ = _ := by rw [input_mesh_product,one_mul]
  have hp : (2:ℝ)^j ≤ (2:ℝ)^(u+9) := by
    have hh := mul_le_mul_of_nonneg_right htop (by positivity : (0:ℝ) ≤ (2:ℝ)^(u+9))
    simpa only [hprod,one_mul] using hh
  have hj := (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2:ℕ))).mp
    (show (2:ℕ)^j ≤ (2:ℕ)^(u+9) by exact_mod_cast hp)
  omega

/-- One choice of eta0, chi and delta0 works for all occupied heights of
one literal Y-key set. No new reference source is selected per height. -/
theorem exists_height_alignment {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃eta0 chi : ℝ,0 < eta0 ∧ 0 < chi ∧
      ∀eta : ℝ,0 < eta → eta ≤ eta0 → ∃delta0 : ℝ,0 < delta0 ∧
      ∀(Y : Finset Key) (u : ℕ) (t : ℝ),
        (2:ℝ)⁻¹^u/512 ≤ delta0 → 0 ≤ t → t ≤ 2 →
        (∀h∈Y.image Prod.fst,∀p∈heightPoints Y ((2:ℝ)⁻¹^u/512) h,
          ∀q∈heightPoints Y ((2:ℝ)⁻¹^u/512) h,dist p q ≤ 1) →
        (∀h∈Y.image Prod.fst,ADBounds (heightPoints Y ((2:ℝ)⁻¹^u/512) h)
          ((2:ℝ)⁻¹^u/512) (((2:ℝ)⁻¹^u/512)^(-eta)) t) →
        Nonempty (∀h : {h : ℤ // h∈Y.image Prod.fst},HeightAlignment Y u t zeta chi h.val) := by
  obtain ⟨eta0,chi,heta0,hchi,H⟩ := native_planar_lemma53 hzeta
  refine ⟨eta0,chi,heta0,hchi,?_⟩
  intro eta heta hetop
  obtain ⟨delta0,hd0,Hplanar⟩ := H eta heta hetop
  refine ⟨delta0,hd0,?_⟩
  intro Y u t hsmall ht ht2 hdiam hAD
  have Hheight (h : {h : ℤ // h∈Y.image Prod.fst}) : Nonempty (HeightAlignment Y u t zeta chi h.val) := by
    obtain ⟨rho,tau,s,j,A,hsub,hne,hrho,hrt,htau,hs,hst,⟨ir,it,hir,hit⟩,
      hgap,hret,_hweak,hpatch⟩ := Hplanar (heightPoints Y ((2:ℝ)⁻¹^u/512) h.val)
        ((2:ℝ)⁻¹^u/512) t (heightPoints_nonempty Y _ h.val h.property)
        (by positivity) hsmall ht ht2 (hdiam h.val h.property) (hAD h.val h.property)
    have hirBound := bounded_depth u ir (by simpa only [hir] using hrt.le.trans htau)
    have hitBound := bounded_depth u it (by simpa only [hit] using htau)
    exact ⟨{
      rhoDepth := ⟨ir,hirBound⟩
      tauDepth := ⟨it,hitBound⟩
      exponent := s
      chart := j
      selected := A
      subset := hsub
      nonempty := hne
      scale_lower := hir ▸ hrho
      scale_order := hir ▸ hit ▸ hrt
      scale_upper := hit ▸ htau
      exponent_nonneg := hs
      exponent_upper := hst
      gap := hir ▸ hit ▸ hgap
      retention := hir ▸ hit ▸ hret
      aligned := hir ▸ hit ▸ hpatch }⟩
  exact ⟨fun h => Classical.choice (Hheight h)⟩

/-- Pull the actual aligned real subset back to the original tagged keys.
Every occupied key in that height survives exactly when its center was selected. -/
theorem pullback_selected (Y : Finset Key) {delta : ℝ} (hd : 0 < delta)
    (h : ℤ) (A : Finset Plane) (hA : A⊆heightPoints Y delta h) :
    let kept := (heightKeys Y h).filter (fun z => center delta z.2∈A)
    kept⊆Y ∧ kept.image (fun z => center delta z.2)=A ∧ kept.card=A.card := by
  intro kept
  have he : kept.image (fun z => center delta z.2)=A := by
    ext x
    constructor
    · intro hx
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp hz).2
    · intro hx
      obtain ⟨z,hz,rfl⟩ := mem_image.mp (hA hx)
      exact mem_image_of_mem _ (mem_filter.mpr ⟨hz,hx⟩)
  refine ⟨(filter_subset _ _).trans (filter_subset _ _),he,?_⟩
  rw [←he]
  symm
  apply card_image_iff.mpr
  intro x hx y hy heq
  have hxheight := (mem_filter.mp (mem_filter.mp hx).1).2
  have hyheight := (mem_filter.mp (mem_filter.mp hy).1).2
  exact Prod.ext (hxheight.trans hyheight.symm) (center_injective hd heq)

/-- The relative retention depends only on the two common dyadic indices,
not on the absolute baseline. -/
def menuFraction {u bins : ℕ} (zeta : ℝ) (c : NativeYCommonScaleSelection.Menu u bins) : ℝ :=
  (((2:ℝ)^c.2.1.val)/((2:ℝ)^c.2.2.1.val))^zeta

lemma scale_ratio {delta : ℝ} (hd : 0 < delta) (ir it : ℕ) :
    scale delta ir / scale delta it = (2:ℝ)^ir/(2:ℝ)^it :=
  mul_div_mul_left _ _ hd.ne'

/-- The common selection is performed on ORIGINAL literal Y-key counts.
Its output retains all planar-selected keys of each surviving height and
therefore keeps the actual local alignment witnesses at that height. The
exponent bin may encode both sides of the later fixed deficit threshold. -/
theorem select_aligned_common (Y : Finset Key) (hY : Y.Nonempty)
    (u bins : ℕ) (t zeta chi : ℝ)
    (W : ∀h : {h : ℤ // h∈Y.image Prod.fst},HeightAlignment Y u t zeta chi h.val)
    (bin : ℝ → Fin (bins+1)) :
    ∃c : NativeYCommonScaleSelection.Menu u bins,∃kept : Finset Key,
      kept⊆Y ∧ kept.Nonempty ∧
      menuFraction zeta c*(Y.card:ℝ) ≤
        (2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ))*(kept.card:ℝ) ∧
      ∀h∈kept.image Prod.fst,∃hh : h∈Y.image Prod.fst,
        (W ⟨h,hh⟩).chart=c.1 ∧ (W ⟨h,hh⟩).rhoDepth=c.2.1 ∧
        (W ⟨h,hh⟩).tauDepth=c.2.2.1 ∧ bin (W ⟨h,hh⟩).exponent=c.2.2.2 ∧
        heightPoints kept ((2:ℝ)⁻¹^u/512) h=(W ⟨h,hh⟩).selected := by
  let delta : ℝ := (2:ℝ)⁻¹^u/512
  have hd : 0 < delta := by dsimp only [delta]; positivity
  let chosen : ℤ → Finset Plane := fun h =>
    if hh : h∈Y.image Prod.fst then (W ⟨h,hh⟩).selected else ∅
  let menu : ℤ → NativeYCommonScaleSelection.Menu u bins := fun h =>
    if hh : h∈Y.image Prod.fst then
      ((W ⟨h,hh⟩).chart,(W ⟨h,hh⟩).rhoDepth,(W ⟨h,hh⟩).tauDepth,bin (W ⟨h,hh⟩).exponent)
    else (0,⟨0,by omega⟩,⟨0,by omega⟩,⟨0,by omega⟩)
  let selected := Y.filter (fun z => center delta z.2∈chosen z.1)
  have hselected : selected⊆Y := filter_subset _ _
  have hSlice (h : ℤ) :
      selected.filter (fun z => z.1=h)=(heightKeys Y h).filter (fun z => center delta z.2∈chosen h) := by
    ext z
    simp only [selected,heightKeys,mem_filter]
    constructor
    · rintro ⟨⟨hz,hsel⟩,hzh⟩
      exact ⟨⟨hz,hzh⟩,by simpa only [hzh] using hsel⟩
    · rintro ⟨⟨hz,hzh⟩,hsel⟩
      exact ⟨⟨hz,by simpa only [hzh] using hsel⟩,hzh⟩
  have hfraction (c : NativeYCommonScaleSelection.Menu u bins) : 0 < menuFraction zeta c := by
    unfold menuFraction
    exact Real.rpow_pos_of_pos (div_pos (by positivity) (by positivity)) _
  have hheight (h : ℤ) (hh : h∈Y.image Prod.fst) :
      menuFraction zeta (menu h)*((Y.filter (fun z => z.1=h)).card:ℝ) ≤
        ((selected.filter (fun z => z.1=h)).card:ℝ) := by
    have hchosen : chosen h=(W ⟨h,hh⟩).selected := by simp only [chosen,dif_pos hh]
    have hmenu : menu h=((W ⟨h,hh⟩).chart,(W ⟨h,hh⟩).rhoDepth,
        (W ⟨h,hh⟩).tauDepth,bin (W ⟨h,hh⟩).exponent) := by simp only [menu,dif_pos hh]
    have hpull := pullback_selected Y hd h (W ⟨h,hh⟩).selected (W ⟨h,hh⟩).subset
    rw [hSlice,hchosen,hpull.2.2,hmenu]
    have hret := (W ⟨h,hh⟩).retention
    rw [heightPoints_card Y hd h,scale_ratio hd] at hret
    exact hret
  obtain ⟨c,hkeep,_href,_hlocal,hret,hmenu,hwhole⟩ :=
    NativeYCommonScaleSelection.variable_retention_select_common u bins Y selected hselected
      menu (menuFraction zeta) (fun c => (hfraction c).le) hheight
  let kept := selected.filter (fun z => menu z.1=c)
  have hkn : kept.Nonempty := by
    apply card_pos.mp
    by_contra hh
    have hz : kept.card=0 := by omega
    change menuFraction zeta c*(Y.card:ℝ) ≤
      (2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ))*(kept.card:ℝ) at hret
    rw [hz,Nat.cast_zero,mul_zero] at hret
    exact (not_le_of_gt (mul_pos (hfraction c) (Nat.cast_pos.mpr hY.card_pos))) hret
  refine ⟨c,kept,hkeep,hkn,hret,?_⟩
  intro h hh
  have hhy : h∈Y.image Prod.fst := image_subset_image hkeep hh
  have hmc : menu h=c := by
    obtain ⟨z,hz,hzh⟩ := mem_image.mp hh
    simpa only [hzh] using hmenu z hz
  have hactual : ((W ⟨h,hhy⟩).chart,(W ⟨h,hhy⟩).rhoDepth,
      (W ⟨h,hhy⟩).tauDepth,bin (W ⟨h,hhy⟩).exponent)=c := by
    simpa only [menu,dif_pos hhy] using hmc
  refine ⟨hhy,congrArg Prod.fst hactual,congrArg (fun x => x.2.1) hactual,
    congrArg (fun x => x.2.2.1) hactual,congrArg (fun x => x.2.2.2) hactual,?_⟩
  unfold heightPoints heightKeys
  rw [hwhole h hh,hSlice]
  have hchosen : chosen h=(W ⟨h,hhy⟩).selected := by simp only [chosen,dif_pos hhy]
  rw [hchosen]
  exact (pullback_selected Y hd h (W ⟨h,hhy⟩).selected (W ⟨h,hhy⟩).subset).2.1

end NativeLiteralYHeightAlignment
