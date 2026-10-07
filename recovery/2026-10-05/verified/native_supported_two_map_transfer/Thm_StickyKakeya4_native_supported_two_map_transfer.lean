import Theorems.Thm_StickyKakeya4_native_two_map_retained_slice_transfer

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

noncomputable section
namespace NativeSupportedTwoMapTransfer
open Classical Finset NativeJointUniformCoarseRelations NativeUniformRetentionTransfer
open NativeRetainedSliceCountTransfer NativeFiniteSliceHomogeneity

/-- Capacities need only hold on the supported pre-third S. The reference
point counts remain those of I, and T is its one retained core. -/
theorem coarse_image_count_le {A X Y Z W : Type*}
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq W]
    (I S T : Finset A) (hSI : S⊆I) (hTS : T⊆S)
    (pref : A → X) (cref : X → Y) (pxy : A → Z) (cxy : Z → W) (Cr : ℕ)
    (hcap : ∀y∈(S.image pref).image cref,
      ((S.filter (fun x => cref (pref x)=y)).image (fun x => cxy (pxy x))).card ≤ Cr) :
    ((T.image pxy).image cxy).card ≤ Cr*((I.image pref).image cref).card := by
  have hh := NativeTwoMapRetainedSliceTransfer.coarse_image_count_le S T hTS pref cref pxy cxy Cr hcap
  exact hh.trans (Nat.mul_le_mul_left Cr (card_le_card (image_subset_image (image_subset_image hSI))))

/-- The lower for an occupied retained XY class uses original-incidence
retention, reference pref uniformity, two geometric map capacities, and the
new XY point/class uniformity on T. The two point maps stay distinct. -/
theorem retained_class_count_cross {A X Y Z W : Type*}
    [DecidableEq A] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq W]
    (I S T : Finset A) (hSI : S⊆I) (hTS : T⊆S) (hIn : I.Nonempty)
    (pref : A → X) (cref : X → Y) (pxy : A → Z) (cxy : Z → W)
    (Qref Qnew C0 Cr : ℕ) (HRef : HasUniformFibers I Qref pref)
    (HP : HasUniformFibers T Qnew pxy)
    (HC : HasUniformFibers T Qnew (fun x => cxy (pxy x)))
    (hfine : ∀z∈T.image pxy,((T.filter (fun x => pxy x=z)).image pref).card ≤ C0)
    (hcoarse : ∀y∈(S.image pref).image cref,
      ((S.filter (fun x => cref (pref x)=y)).image (fun x => cxy (pxy x))).card ≤ Cr)
    (lambda loss : ℝ) (hloss : 0 ≤ loss) (hret : lambda*(I.card:ℝ) ≤ loss*T.card)
    (u : W) (hu : u∈(T.image pxy).image cxy) :
    lambda*(I.image pref).card ≤
      loss*(Qref:ℝ)^2*C0*Cr*(Qnew:ℝ)^4*
        ((T.image pxy).filter (fun z => cxy z=u)).card*((I.image pref).image cref).card := by
  have hpoint := NativeTwoMapRetainedSliceTransfer.point_image_retention I T (hTS.trans hSI) hIn pref pxy Qref C0 HRef hfine lambda loss hloss hret
  have hclass := coarse_image_count_le I S T hSI hTS pref cref pxy cxy Cr hcoarse
  have havg := (fiber_card_average_cross (T.image pxy) cxy (Qnew^4)
    (point_class_homogeneity T pxy cxy Qnew HP HC) u hu).2
  have hlocal : ((T.image pxy).card:ℝ) ≤
      (Cr:ℝ)*(Qnew:ℝ)^4*((T.image pxy).filter (fun z => cxy z=u)).card*
        ((I.image pref).image cref).card := by
    have hh := havg.trans (Nat.mul_le_mul_left _ hclass)
    have hhR : ((T.image pxy).card:ℝ) ≤
        (Qnew:ℝ)^4*((T.image pxy).filter (fun z => cxy z=u)).card*
          ((Cr:ℝ)*((I.image pref).image cref).card) := by exact_mod_cast hh
    exact hhR.trans_eq (by ring)
  calc
    _ ≤ loss*(Qref:ℝ)^2*C0*(T.image pxy).card := hpoint
    _ ≤ loss*(Qref:ℝ)^2*C0*((Cr:ℝ)*(Qnew:ℝ)^4*((T.image pxy).filter (fun z => cxy z=u)).card*
        ((I.image pref).image cref).card) :=
      mul_le_mul_of_nonneg_left hlocal (by positivity)
    _ = _ := by ring

/-- A reference fine/coarse ratio yields the retained XY class lower,
without any reference XY uniformity or already assumed XY regularity. -/
theorem retained_class_count_lower {A X Y Z W : Type*}
    [DecidableEq A] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq W]
    (I S T : Finset A) (hSI : S⊆I) (hTS : T⊆S) (hIn : I.Nonempty)
    (pref : A → X) (cref : X → Y) (pxy : A → Z) (cxy : Z → W)
    (Qref Qnew C0 Cr : ℕ) (HRef : HasUniformFibers I Qref pref)
    (HP : HasUniformFibers T Qnew pxy)
    (HC : HasUniformFibers T Qnew (fun x => cxy (pxy x)))
    (hfine : ∀z∈T.image pxy,((T.filter (fun x => pxy x=z)).image pref).card ≤ C0)
    (hcoarse : ∀y∈(S.image pref).image cref,
      ((S.filter (fun x => cref (pref x)=y)).image (fun x => cxy (pxy x))).card ≤ Cr)
    (lambda loss lower : ℝ) (hlambda : 0 ≤ lambda) (hloss : 0 ≤ loss)
    (hret : lambda*(I.card:ℝ) ≤ loss*T.card)
    (hRatio : lower*((I.image pref).image cref).card ≤ (I.image pref).card)
    (u : W) (hu : u∈(T.image pxy).image cxy) :
    lambda*lower ≤ loss*(Qref:ℝ)^2*C0*Cr*(Qnew:ℝ)^4*((T.image pxy).filter (fun z => cxy z=u)).card := by
  have hcross := retained_class_count_cross I S T hSI hTS hIn pref cref pxy cxy Qref Qnew C0 Cr
    HRef HP HC hfine hcoarse lambda loss hloss hret u hu
  have hCp : (0:ℝ)<((I.image pref).image cref).card :=
    Nat.cast_pos.mpr (card_pos.mpr ((hIn.image pref).image cref))
  apply (mul_le_mul_iff_left₀ hCp).mp
  calc
    _ = lambda*(lower*((I.image pref).image cref).card) := by ring
    _ ≤ lambda*(I.image pref).card := mul_le_mul_of_nonneg_left hRatio hlambda
    _ ≤ _ := hcross

end NativeSupportedTwoMapTransfer
