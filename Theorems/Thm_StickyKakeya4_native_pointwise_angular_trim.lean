import Theorems.Thm_StickyKakeya4_native_automatic_weighted_grain_core

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000
noncomputable section
namespace NativePointwiseAngularTrim
open Classical Finset NativeAutomaticWeightedGrainCore
open RichDirectionalLayers WeightedRichDirectionalLayers
open scoped BigOperators

/-- Refine directions independently at every ORIGINAL point. Every spatial
point survives; every point keeps half its original incidence weight. Dense
angular classes are obtained simultaneously, with their own level counts. -/
theorem exists_pointwise_angular_core {A X : Type*} [DecidableEq A] [DecidableEq X]
    {J : ℕ} {B : Fin J → Type*} (hJ : 0 < J)
    (I : Finset (A × X)) (f : (j : Fin J) → (A × X) → B j) :
    ∃T⊆I,T.image Prod.snd=I.image Prod.snd ∧ I.card ≤ 2*T.card ∧
      (∀x∈I.image Prod.snd,(I.filter (fun z => z.2=x)).card ≤
        2*(T.filter (fun z => z.2=x)).card) ∧
      ∀x∈T.image Prod.snd,∀j,∀c∈((T.filter (fun z => z.2=x)).image (f j)),
        threshold (I.filter (fun z => z.2=x)).card J
          (((I.filter (fun z => z.2=x)).image (f j)).card) ≤
          (classFiber (T.filter (fun z => z.2=x)) (f j) c).card ∧
        ((I.filter (fun z => z.2=x)).card:ℝ)/
          (2*(J:ℝ)*(((I.filter (fun z => z.2=x)).image (f j)).card:ℝ)) <
          ((classFiber (T.filter (fun z => z.2=x)) (f j) c).card:ℝ) := by
  let P := I.image Prod.snd
  have hex (x : P) := exists_automatic_simultaneous_dense_core hJ
    (I.filter (fun z => z.2=x.val)) f (fun _ => 1) (by
      have hx : (I.filter (fun z => z.2=x.val)).Nonempty := by
        obtain ⟨z,hz,he⟩ := mem_image.mp x.property
        exact ⟨z,mem_filter.mpr ⟨hz,he⟩⟩
      simpa only [WeightedRichDirectionalLayers.mass,sum_const,smul_eq_mul,mul_one] using card_pos.mpr hx)
  choose K hKI hKn hhalf hdeleted hmin using hex
  let T := P.attach.biUnion K
  have hTI : T⊆I := by
    intro z hz
    obtain ⟨x,_hx,hzx⟩ := mem_biUnion.mp hz
    exact (mem_filter.mp (hKI x hzx)).1
  have hfilter (x : P) : T.filter (fun z => z.2=x.val)=K x := by
    ext z
    constructor
    · intro hz
      obtain ⟨hz,hpt⟩ := mem_filter.mp hz
      obtain ⟨y,_hy,hzy⟩ := mem_biUnion.mp hz
      have hyx : y=x := Subtype.ext ((mem_filter.mp (hKI y hzy)).2.symm.trans hpt)
      simpa only [hyx] using hzy
    · intro hz
      exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨x,mem_attach P x,hz⟩,(mem_filter.mp (hKI x hz)).2⟩
  have hpoints : T.image Prod.snd=P := by
    apply Subset.antisymm (image_subset_image hTI)
    intro x hx
    obtain ⟨z,hz⟩ := hKn ⟨x,hx⟩
    exact mem_image.mpr ⟨z,mem_biUnion.mpr ⟨⟨x,hx⟩,mem_attach P _,hz⟩,
      (mem_filter.mp (hKI ⟨x,hx⟩ hz)).2⟩
  have hlocal (x : X) (hx : x∈P) : (I.filter (fun z => z.2=x)).card ≤
      2*(T.filter (fun z => z.2=x)).card := by
    have hh := hhalf ⟨x,hx⟩
    rw [hfilter ⟨x,hx⟩]
    simpa only [WeightedRichDirectionalLayers.mass,sum_const,smul_eq_mul,mul_one] using hh
  refine ⟨T,hTI,hpoints,?_,hlocal,?_⟩
  · calc
      I.card = ∑x∈P,(I.filter (fun z => z.2=x)).card := card_eq_sum_card_image Prod.snd I
      _ ≤ ∑x∈P,2*(T.filter (fun z => z.2=x)).card := sum_le_sum hlocal
      _ = 2*T.card := by
        rw [←mul_sum,←hpoints,←card_eq_sum_card_image Prod.snd T]
  · intro x hx j c hc
    have hxP : x∈P := hpoints ▸ hx
    rw [hfilter ⟨x,hxP⟩] at hc ⊢
    simpa only [WeightedRichDirectionalLayers.mass,sum_const,smul_eq_mul,mul_one] using hmin ⟨x,hxP⟩ j c hc

/-- Any geometry determined by original point labels is literally unchanged,
including raw vertices, XY points and point-dependent grain-coordinate sets. -/
theorem point_image_unchanged {A X Y : Type*} [DecidableEq A] [DecidableEq X] [DecidableEq Y]
    (I T : Finset (A × X)) (hpoints : T.image Prod.snd=I.image Prod.snd) (g : X → Y) :
    T.image (fun z => g z.2)=I.image (fun z => g z.2) := by
  simpa only [image_image,Function.comp_def] using congrArg (fun P : Finset X => P.image g) hpoints

end NativePointwiseAngularTrim
