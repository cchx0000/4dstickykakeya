import Theorems.Thm_StickyKakeya4_native_two_map_retained_slice_transfer
import Theorems.Thm_StickyKakeya4_native_retained_grain_density_core

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

noncomputable section
namespace NativeTwoMapRetainedSliceCore
open Classical Finset SelfUniform NativeJointUniformCoarseRelations
open NativeRetainedSliceCore NativeRetainedGrainDensityCore NativeRetainedGrainDensityTransfer
open NativeTwoMapRetainedSliceTransfer

/-- One third refinement on the original S-incidences constructs XY point,
XY class and old-grain uniformity simultaneously. Only pref is uniform on
the reference I. Both coordinate maps are fixed on I before this selection;
their geometric capacities are inherited by every retained subset. -/
theorem exists_two_map_slice_grain_core {A X Y Z W V V' : Type*}
    [DecidableEq A] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq W] [DecidableEq V]
    {d K : ℕ} (I H S : Finset A) (hHI : H⊆I) (hSH : S⊆H) (hSn : S.Nonempty)
    (pref : A → X) (cref : Fin K → X → Y) (pxy : A → Z) (cxy : Fin K → Z → W)
    (grain : A → V) (quotient : A → V')
    (hquotient : ∀x y,x∈S → y∈S → grain x=grain y → quotient x=quotient y)
    (Qref C0 : ℕ) (Cr : Fin K → ℕ) (HRef : HasUniformFibers I Qref pref)
    (hfine : ∀z∈I.image pxy,((I.filter (fun x => pxy x=z)).image pref).card ≤ C0)
    (hcoarse : ∀j y,y∈(I.image pref).image (cref j) →
      ((I.filter (fun x => cref j (pref x)=y)).image (fun x => cxy j (pxy x))).card ≤ Cr j)
    (lambda G Cq t : ℝ) (hlambda : 0 ≤ lambda) (hG : 0 ≤ G) (hCq : 0 ≤ Cq)
    (hret : lambda*(I.card:ℝ) ≤ G*H.card) (hquotientRet : (H.card:ℝ) ≤ Cq*S.card)
    (hgrain : ∀g∈H.image grain,t ≤ ((H.filter (fun z => grain z=g)).card:ℝ))
    (lower : Fin K → ℝ)
    (hRatio : ∀j,lower j*((I.image pref).image (cref j)).card ≤ (I.image pref).card)
    (Rel : Fin d → A → A → Prop) (hrefl : ∀j x,Rel j x x)
    (hsym : ∀j x y,Rel j x y → Rel j y x) (L : ℕ) (hL : 0 < L) :
    let Q := NativeSourceSizeBounds.radix S.card L
    let F := refinementCost (d+1) K L
    ∃T⊆S,T.Nonempty ∧ S.card ≤ F*T.card ∧
      (∀j x y,x∈T → y∈T → degree (fun _ : A => 1) (Rel j) T x ≤
        Q^2*degree (fun _ : A => 1) (Rel j) T y) ∧
      HasUniformFibers T Q pxy ∧
      (∀j,HasUniformFibers T Q (fun x => cxy j (pxy x))) ∧
      HasUniformFibers T Q grain ∧
      (∀x y,x∈T → y∈T → grain x=grain y → quotient x=quotient y) ∧
      (∀g∈T.image grain,t ≤ Cq*(F:ℝ)*(Q:ℝ)^2*(T.filter (fun x => grain x=g)).card) ∧
      lambda*(I.image pref).card ≤
        G*Cq*(F:ℝ)*(Qref:ℝ)^2*C0*(T.image pxy).card ∧
      ∀j,((T.image pxy).image (cxy j)).card ≤ Cr j*((I.image pref).image (cref j)).card ∧
        ∀u,u∈(T.image pxy).image (cxy j) →
          lambda*lower j ≤ G*Cq*(F:ℝ)*(Qref:ℝ)^2*C0*(Cr j)*(Q:ℝ)^4*
            ((T.image pxy).filter (fun z => cxy j z=u)).card := by
  intro Q F
  obtain ⟨T,hTS,hTn,hcost,hExtra,hPoint,hClass⟩ :=
    exists_retained_slice_core S hSn pxy cxy (grainRelations grain Rel)
      (grainRelations_refl grain Rel hrefl) (grainRelations_symm grain Rel hsym) L hL
  have hTI : T⊆I := hTS.trans (hSH.trans hHI)
  have hIn : I.Nonempty := hSn.mono (hSH.trans hHI)
  have hfineT : ∀z∈T.image pxy,((T.filter (fun x => pxy x=z)).image pref).card ≤ C0 := by
    intro z hz
    exact (card_le_card (image_subset_image (filter_subset_filter _ hTI))).trans
      (hfine z (image_subset_image hTI hz))
  have hcostR : (S.card:ℝ) ≤ (F:ℝ)*T.card := by exact_mod_cast hcost
  have hretT : lambda*(I.card:ℝ) ≤ (G*Cq*(F:ℝ))*T.card := by
    calc
      _ ≤ G*H.card := hret
      _ ≤ G*(Cq*S.card) := mul_le_mul_of_nonneg_left hquotientRet hG
      _ = (G*Cq)*(S.card:ℝ) := by ring
      _ ≤ (G*Cq)*((F:ℝ)*T.card) := mul_le_mul_of_nonneg_left hcostR (mul_nonneg hG hCq)
      _ = _ := by ring
  have hLoss : 0 ≤ G*Cq*(F:ℝ) := mul_nonneg (mul_nonneg hG hCq) (Nat.cast_nonneg _)
  have hGrain : HasUniformFibers T Q grain := by
    apply extra_relation_grain_uniformity T Q grain (grainRelations grain Rel) (Fin.natAdd d (0:Fin 1))
      (fun x y => ?_) (hExtra (Fin.natAdd d (0:Fin 1)))
    simp only [grainRelations,Fin.addCases_right]
  refine ⟨T,hTS,hTn,hcost,?_,hPoint,hClass,hGrain,?_,?_,?_,?_⟩
  · intro j x y hx hy
    simpa only [grainRelations,Fin.addCases_left] using hExtra (Fin.castAdd 1 j) x y hx hy
  · intro x y hx hy hxy
    exact hquotient x y (hTS hx) (hTS hy) hxy
  · intro g hg
    exact retained_grain_density_two_stage H S T hSH hTS grain Q hGrain t Cq F hCq
      (Nat.cast_nonneg _) hgrain hquotientRet hcostR g hg
  · exact NativeTwoMapRetainedSliceTransfer.point_image_retention I T hTI hIn pref pxy Qref C0
      HRef hfineT lambda (G*Cq*(F:ℝ)) hLoss hretT
  · intro j
    refine ⟨coarse_image_count_le I T hTI pref (cref j) pxy (cxy j) (Cr j) (hcoarse j),?_⟩
    intro u hu
    exact NativeTwoMapRetainedSliceTransfer.retained_class_count_lower I T hTI hIn
      pref (cref j) pxy (cxy j) Qref Q C0 (Cr j) HRef hPoint (hClass j) hfineT (hcoarse j)
      lambda (G*Cq*(F:ℝ)) (lower j) hlambda hLoss hretT (hRatio j) u hu

end NativeTwoMapRetainedSliceCore
