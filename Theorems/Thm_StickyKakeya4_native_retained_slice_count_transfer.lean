import Theorems.Thm_StickyKakeya4_native_finite_slice_homogeneity
import Theorems.Thm_StickyKakeya4_native_uniform_retention_transfer

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeRetainedSliceCountTransfer
open Classical Finset NativeJointUniformCoarseRelations NativeCoarseShadingUniformity
open NativeUniformRetentionTransfer NativeFiniteSliceHomogeneity

/-- Original incidence retention, together with the reference's actual
point weights, retains distinct finest points without a dimension loss. -/
theorem point_image_retention {A X : Type*} [DecidableEq A] [DecidableEq X]
    (I H : Finset A) (hHI : H⊆I) (hIn : I.Nonempty) (point : A → X) (Q : ℕ)
    (HU : HasUniformFibers I Q point) (lambda G : ℝ) (hG : 0 ≤ G)
    (hret : lambda*(I.card:ℝ) ≤ G*H.card) :
    lambda*(I.image point).card ≤ G*(Q:ℝ)^2*(H.image point).card := by
  have hcross : (H.card:ℝ)*(I.image point).card ≤
      (Q:ℝ)^2*I.card*(H.image point).card := by
    exact_mod_cast uniform_subset_card_cross I H hHI point Q HU
  have hIp : (0:ℝ)<I.card := Nat.cast_pos.mpr (card_pos.mpr hIn)
  apply (mul_le_mul_iff_right₀ hIp).mp
  calc
    _ = (lambda*(I.card:ℝ))*(I.image point).card := by ring
    _ ≤ (G*(H.card:ℝ))*(I.image point).card :=
      mul_le_mul_of_nonneg_right hret (Nat.cast_nonneg _)
    _ = G*((H.card:ℝ)*(I.image point).card) := by ring
    _ ≤ G*((Q:ℝ)^2*I.card*(H.image point).card) := mul_le_mul_of_nonneg_left hcross hG
    _ = _ := by ring

/-- New incidence uniformity is converted to homogeneity of the actual
distinct point classes. Every point still comes from a retained original label. -/
theorem point_class_homogeneity {A X Y : Type*}
    [DecidableEq A] [DecidableEq X] [DecidableEq Y]
    (H : Finset A) (point : A → X) (cls : X → Y) (Q : ℕ)
    (HP : HasUniformFibers H Q point)
    (HC : HasUniformFibers H Q (fun z => cls (point z))) :
    ∀x∈H.image point,∀y∈H.image point,
      ((H.image point).filter (fun z => cls z=cls x)).card ≤
        Q^4*((H.image point).filter (fun z => cls z=cls y)).card := by
  intro x hx y hy
  have hh := nested_image_fiber_card_comparable H point cls (Q^2) (Q^2) HP HC
    (cls x) (cls y) (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)
  simpa only [show Q^2*Q^2=Q^4 by ring] using hh

/-- Post-cut class lower counts are derived from retained original mass,
reference point uniformity, and newly constructed point/class uniformity.
The reference coarse covering count is only an upper denominator. -/
theorem retained_class_count_cross {A X Y : Type*}
    [DecidableEq A] [DecidableEq X] [DecidableEq Y]
    (I H : Finset A) (hHI : H⊆I) (hIn : I.Nonempty)
    (point : A → X) (cls : X → Y) (Qref Qnew : ℕ)
    (HRef : HasUniformFibers I Qref point)
    (HP : HasUniformFibers H Qnew point)
    (HC : HasUniformFibers H Qnew (fun z => cls (point z)))
    (lambda G : ℝ) (hG : 0 ≤ G) (hret : lambda*(I.card:ℝ) ≤ G*H.card)
    (t : Y) (ht : t∈(H.image point).image cls) :
    lambda*(I.image point).card ≤
      G*(Qref:ℝ)^2*(Qnew:ℝ)^4*
        ((H.image point).filter (fun z => cls z=t)).card*((I.image point).image cls).card ∧
      ((H.image point).filter (fun z => cls z=t)).card ≤
        ((I.image point).filter (fun z => cls z=t)).card := by
  have himage : H.image point⊆I.image point := image_subset_image hHI
  have hclass : ((H.image point).image cls).card ≤ ((I.image point).image cls).card :=
    card_le_card (image_subset_image himage)
  have hpoint := point_image_retention I H hHI hIn point Qref HRef lambda G hG hret
  have havg := (fiber_card_average_cross (H.image point) cls (Qnew^4)
    (point_class_homogeneity H point cls Qnew HP HC) t ht).2
  have hlocal : ((H.image point).card:ℝ) ≤
      (Qnew:ℝ)^4*((H.image point).filter (fun z => cls z=t)).card*
        ((I.image point).image cls).card := by
    have hh : (H.image point).card ≤ Qnew^4*((H.image point).filter (fun z => cls z=t)).card*
        ((I.image point).image cls).card :=
      havg.trans (Nat.mul_le_mul_left _ hclass)
    exact_mod_cast hh
  refine ⟨?_,card_le_card (filter_subset_filter _ himage)⟩
  calc
    _ ≤ G*(Qref:ℝ)^2*(H.image point).card := hpoint
    _ ≤ G*(Qref:ℝ)^2*((Qnew:ℝ)^4*((H.image point).filter (fun z => cls z=t)).card*
        ((I.image point).image cls).card) :=
      mul_le_mul_of_nonneg_left hlocal (mul_nonneg hG (sq_nonneg _))
    _ = _ := by ring

/-- A reference fine/coarse count ratio supplies the desired retained local
lower. No retained-set AD or rich-class hypothesis is assumed. -/
theorem retained_class_count_lower {A X Y : Type*}
    [DecidableEq A] [DecidableEq X] [DecidableEq Y]
    (I H : Finset A) (hHI : H⊆I) (hIn : I.Nonempty)
    (point : A → X) (cls : X → Y) (Qref Qnew : ℕ)
    (HRef : HasUniformFibers I Qref point)
    (HP : HasUniformFibers H Qnew point)
    (HC : HasUniformFibers H Qnew (fun z => cls (point z)))
    (lambda G L : ℝ) (hlambda : 0 ≤ lambda) (hG : 0 ≤ G)
    (hret : lambda*(I.card:ℝ) ≤ G*H.card)
    (hRatio : L*((I.image point).image cls).card ≤ (I.image point).card)
    (t : Y) (ht : t∈(H.image point).image cls) :
    lambda*L ≤ G*(Qref:ℝ)^2*(Qnew:ℝ)^4*((H.image point).filter (fun z => cls z=t)).card := by
  have hcross := (retained_class_count_cross I H hHI hIn point cls Qref Qnew HRef HP HC
    lambda G hG hret t ht).1
  have htref : t∈(I.image point).image cls := image_subset_image (image_subset_image hHI) ht
  have hCp : (0:ℝ)<((I.image point).image cls).card :=
    Nat.cast_pos.mpr (card_pos.mpr ⟨t,htref⟩)
  apply (mul_le_mul_iff_left₀ hCp).mp
  calc
    _ = lambda*(L*((I.image point).image cls).card) := by ring
    _ ≤ lambda*(I.image point).card := mul_le_mul_of_nonneg_left hRatio hlambda
    _ ≤ _ := hcross

end NativeRetainedSliceCountTransfer
