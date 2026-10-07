import Theorems.Thm_StickyKakeya4_native_two_map_retained_slice_transfer

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeTwoMapRetainedSliceUpper
open Classical Finset NativeUniformRetentionTransfer

/-- A local XY class is controlled by a fine forward-map capacity and a
coarse inverse-map capacity. This does not identify the two point sets or
assume uniformity of XY labels on the reference. -/
theorem retained_class_upper {A X Y Z W : Type*}
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq W]
    (I T : Finset A) (hTI : T⊆I)
    (pref : A → X) (cref : X → Y) (pxy : A → Z) (cxy : Z → W)
    (C1 C2 : ℕ) (U : ℝ) (hU : 0 ≤ U)
    (hfine : ∀x∈I.image pref,((I.filter (fun z => pref z=x)).image pxy).card ≤ C1)
    (hinverse : ∀u∈I.image (fun z => cxy (pxy z)),
      ((I.filter (fun z => cxy (pxy z)=u)).image (fun z => cref (pref z))).card ≤ C2)
    (hRef : ∀y∈(I.image pref).image cref,
      (((I.image pref).filter (fun x => cref x=y)).card:ℝ) ≤ U)
    (u : W) :
    (((T.image pxy).filter (fun z => cxy z=u)).card:ℝ) ≤ (C1:ℝ)*C2*U := by
  let S := T.filter (fun z => cxy (pxy z)=u)
  have hSI : S⊆I := (filter_subset _ _).trans hTI
  have he : (T.image pxy).filter (fun z => cxy z=u)=S.image pxy := by
    rw [filter_image]
  rw [he]
  by_cases hSn : S.Nonempty
  · have hFine : (S.image pxy).card ≤ C1*(S.image pref).card :=
      image_card_le_mul_of_fiber_images S pxy pref C1 (by
        intro x hx
        exact (card_le_card (image_subset_image (filter_subset_filter _ hSI))).trans
          (hfine x (image_subset_image hSI hx)))
    have hCoarse : (S.image (fun z => cref (pref z))).card ≤ C2 := by
      have hs : S⊆I.filter (fun z => cxy (pxy z)=u) := by
        intro z hz
        exact mem_filter.mpr ⟨hSI hz,(mem_filter.mp hz).2⟩
      obtain ⟨z,hz⟩ := hSn
      apply (card_le_card (image_subset_image hs)).trans (hinverse u ?_)
      exact mem_image.mpr ⟨z,hSI hz,(mem_filter.mp hz).2⟩
    have hLocal := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images
      S pref (fun z => cref (pref z)) U (by
        intro y hy
        have hs : (S.filter (fun z => cref (pref z)=y)).image pref⊆
            (I.image pref).filter (fun x => cref x=y) := by
          intro x hx
          obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
          exact mem_filter.mpr ⟨mem_image_of_mem _ (hSI (mem_filter.mp hz).1),(mem_filter.mp hz).2⟩
        apply (Nat.cast_le.mpr (card_le_card hs)).trans (hRef y ?_)
        simpa only [image_image,Function.comp_def] using image_subset_image hSI hy)
    have hLocal' : ((S.image pref).card:ℝ) ≤ U*C2 :=
      hLocal.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hCoarse) hU)
    have hFineR : ((S.image pxy).card:ℝ) ≤ (C1:ℝ)*(S.image pref).card := by exact_mod_cast hFine
    exact hFineR.trans ((mul_le_mul_of_nonneg_left hLocal' (Nat.cast_nonneg _)).trans_eq (by ring))
  · rw [not_nonempty_iff_eq_empty.mp hSn,image_empty,card_empty,Nat.cast_zero]
    positivity

end NativeTwoMapRetainedSliceUpper
