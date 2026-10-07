import Theorems.Thm_StickyKakeya4_native_two_map_retained_slice_transfer

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeSupportedTwoMapUpper
open Classical Finset NativeUniformRetentionTransfer

/-- A local XY class is controlled by a fine forward-map capacity and a
coarse inverse-map capacity. This does not identify the two point sets or
assume uniformity of XY labels on the reference. -/
theorem retained_class_upper {A X Y Z W : Type*}
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq W]
    (I S T : Finset A) (hSI : S⊆I) (hTS : T⊆S)
    (pref : A → X) (cref : X → Y) (pxy : A → Z) (cxy : Z → W)
    (C1 C2 : ℕ) (U : ℝ) (hU : 0 ≤ U)
    (hfine : ∀x∈S.image pref,((S.filter (fun z => pref z=x)).image pxy).card ≤ C1)
    (hinverse : ∀u∈S.image (fun z => cxy (pxy z)),
      ((S.filter (fun z => cxy (pxy z)=u)).image (fun z => cref (pref z))).card ≤ C2)
    (hRef : ∀y∈(I.image pref).image cref,
      (((I.image pref).filter (fun x => cref x=y)).card:ℝ) ≤ U)
    (u : W) :
    (((T.image pxy).filter (fun z => cxy z=u)).card:ℝ) ≤ (C1:ℝ)*C2*U := by
  let V := T.filter (fun z => cxy (pxy z)=u)
  have hVI : V⊆I := (filter_subset _ _).trans (hTS.trans hSI)
  have hVS : V⊆S := (filter_subset _ _).trans hTS
  have he : (T.image pxy).filter (fun z => cxy z=u)=V.image pxy := by
    rw [filter_image]
  rw [he]
  by_cases hSn : V.Nonempty
  · have hFine : (V.image pxy).card ≤ C1*(V.image pref).card :=
      image_card_le_mul_of_fiber_images V pxy pref C1 (by
        intro x hx
        exact (card_le_card (image_subset_image (filter_subset_filter _ hVS))).trans
          (hfine x (image_subset_image hVS hx)))
    have hCoarse : (V.image (fun z => cref (pref z))).card ≤ C2 := by
      have hs : V⊆S.filter (fun z => cxy (pxy z)=u) := by
        intro z hz
        exact mem_filter.mpr ⟨hVS hz,(mem_filter.mp hz).2⟩
      obtain ⟨z,hz⟩ := hSn
      apply (card_le_card (image_subset_image hs)).trans (hinverse u ?_)
      exact mem_image.mpr ⟨z,hVS hz,(mem_filter.mp hz).2⟩
    have hLocal := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images
      V pref (fun z => cref (pref z)) U (by
        intro y hy
        have hs : (V.filter (fun z => cref (pref z)=y)).image pref⊆
            (I.image pref).filter (fun x => cref x=y) := by
          intro x hx
          obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
          exact mem_filter.mpr ⟨mem_image_of_mem _ (hVI (mem_filter.mp hz).1),(mem_filter.mp hz).2⟩
        apply (Nat.cast_le.mpr (card_le_card hs)).trans (hRef y ?_)
        simpa only [image_image,Function.comp_def] using image_subset_image hVI hy)
    have hLocal' : ((V.image pref).card:ℝ) ≤ U*C2 :=
      hLocal.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hCoarse) hU)
    have hFineR : ((V.image pxy).card:ℝ) ≤ (C1:ℝ)*(V.image pref).card := by exact_mod_cast hFine
    exact hFineR.trans ((mul_le_mul_of_nonneg_left hLocal' (Nat.cast_nonneg _)).trans_eq (by ring))
  · rw [not_nonempty_iff_eq_empty.mp hSn,image_empty,card_empty,Nat.cast_zero]
    positivity



theorem height_image_cap {A X Y H : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq H]
    (I S T : Finset A) (hSI : S⊆I) (hTS : T⊆S) (f : A → X) (g : A → Y)
    (hf : X → H) (hg : Y → H)
    (hheight : ∀a∈T,hf (f a)=hg (g a)) (C N : ℕ)
    (hcap : ∀y∈S.image g,((S.filter (fun a => g a=y)).image f).card ≤ C)
    (hEnd : ∀t,((I.image g).filter (fun y => hg y=t)).card ≤ N) (t : H) :
    ((T.image f).filter (fun x => hf x=t)).card ≤ C*N := by
  let V := T.filter (fun a => hf (f a)=t)
  have hVI : V⊆I := (filter_subset _ _).trans (hTS.trans hSI)
  have hVS : V⊆S := (filter_subset _ _).trans hTS
  have he : (T.image f).filter (fun x => hf x=t)=V.image f := by rw [filter_image]
  rw [he]
  have hc : (V.image f).card ≤ C*(V.image g).card :=
    image_card_le_mul_of_fiber_images V f g C (by
      intro y hy
      exact (card_le_card (image_subset_image (filter_subset_filter _ hVS))).trans
        (hcap y (image_subset_image hVS hy)))
  have hs : V.image g⊆(I.image g).filter (fun y => hg y=t) := by
    intro y hy
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hy
    exact mem_filter.mpr ⟨mem_image_of_mem _ (hVI ha),
      (hheight a (mem_filter.mp ha).1).symm.trans (mem_filter.mp ha).2⟩
  exact hc.trans (Nat.mul_le_mul_left C ((card_le_card hs).trans (hEnd t)))

end NativeSupportedTwoMapUpper
