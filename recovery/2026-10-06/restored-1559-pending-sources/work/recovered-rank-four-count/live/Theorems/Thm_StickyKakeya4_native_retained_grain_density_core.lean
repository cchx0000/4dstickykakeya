import Theorems.Thm_StickyKakeya4_native_retained_grain_density_transfer

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

noncomputable section
namespace NativeRetainedGrainDensityCore
open Classical Finset SelfUniform NativeJointUniformCoarseRelations
open NativeRetainedSliceCore NativeRetainedGrainDensityTransfer

/-- Add old-grain equality to the third core's other quotient/grain relations. -/
def grainRelations {A Y : Type*} {d : ℕ} (grain : A → Y)
    (Rel : Fin d → A → A → Prop) : Fin (d+1) → A → A → Prop :=
  Fin.addCases Rel (fun _ : Fin 1 => fun x y => grain x=grain y)

lemma grainRelations_refl {A Y : Type*} {d : ℕ} (grain : A → Y)
    (Rel : Fin d → A → A → Prop) (hrefl : ∀j x,Rel j x x) :
    ∀j x,grainRelations grain Rel j x x := by
  intro j x
  refine Fin.addCases ?_ ?_ j
  · intro i
    simpa only [grainRelations,Fin.addCases_left] using hrefl i x
  · intro i
    simp only [grainRelations,Fin.addCases_right]

lemma grainRelations_symm {A Y : Type*} {d : ℕ} (grain : A → Y)
    (Rel : Fin d → A → A → Prop) (hsym : ∀j x y,Rel j x y → Rel j y x) :
    ∀j x y,grainRelations grain Rel j x y → grainRelations grain Rel j y x := by
  intro j x y
  refine Fin.addCases ?_ ?_ j
  · intro i hh
    simp only [grainRelations,Fin.addCases_left] at hh ⊢
    exact hsym i x y hh
  · intro i hh
    simp only [grainRelations,Fin.addCases_right] at hh ⊢
    exact hh.symm

/-- ONE third refinement simultaneously supplies the retained slice counts
and reconstructs every surviving original grain's density. A quotient already
chosen on S stays unique in every old grain by literal inclusion. -/
theorem exists_slice_grain_core {A X Y Z V : Type*}
    [DecidableEq A] [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    {d K : ℕ} (I H S : Finset A) (hHI : H⊆I) (hSH : S⊆H) (hSn : S.Nonempty)
    (point : A → X) (classes : Fin K → X → Y) (grain : A → Z) (quotient : A → V)
    (hquotient : ∀x y,x∈S → y∈S → grain x=grain y → quotient x=quotient y)
    (Qref : ℕ) (HRef : HasUniformFibers I Qref point)
    (lambda G Cq t : ℝ) (hlambda : 0 ≤ lambda) (hG : 0 ≤ G) (hCq : 0 ≤ Cq)
    (hret : lambda*(I.card:ℝ) ≤ G*H.card) (hquotientRet : (H.card:ℝ) ≤ Cq*S.card)
    (hgrain : ∀g∈H.image grain,t ≤ ((H.filter (fun z => grain z=g)).card:ℝ))
    (lower : Fin K → ℝ)
    (hRatio : ∀j,lower j*((I.image point).image (classes j)).card ≤ (I.image point).card)
    (Rel : Fin d → A → A → Prop) (hrefl : ∀j x,Rel j x x)
    (hsym : ∀j x y,Rel j x y → Rel j y x) (L : ℕ) (hL : 0 < L) :
    let Q := NativeSourceSizeBounds.radix S.card L
    let F := refinementCost (d+1) K L
    ∃T⊆S,T.Nonempty ∧ S.card ≤ F*T.card ∧
      (∀j x y,x∈T → y∈T → degree (fun _ : A => 1) (Rel j) T x ≤
        Q^2*degree (fun _ : A => 1) (Rel j) T y) ∧
      HasUniformFibers T Q point ∧
      (∀j,HasUniformFibers T Q (fun z => classes j (point z))) ∧
      HasUniformFibers T Q grain ∧
      (∀x y,x∈T → y∈T → grain x=grain y → quotient x=quotient y) ∧
      (∀g∈T.image grain,t ≤ Cq*(F:ℝ)*(Q:ℝ)^2*(T.filter (fun z => grain z=g)).card) ∧
      lambda*(I.image point).card ≤
        G*Cq*(F:ℝ)*(Qref:ℝ)^2*(T.image point).card ∧
      ∀j u,u∈(T.image point).image (classes j) →
        lambda*lower j ≤ G*Cq*(F:ℝ)*(Qref:ℝ)^2*(Q:ℝ)^4*
          ((T.image point).filter (fun z => classes j z=u)).card ∧
        ((T.image point).filter (fun z => classes j z=u)).card ≤
          ((I.image point).filter (fun z => classes j z=u)).card := by
  intro Q F
  have hretS : lambda*(I.card:ℝ) ≤ (G*Cq)*S.card :=
    hret.trans ((mul_le_mul_of_nonneg_left hquotientRet hG).trans_eq (by ring))
  obtain ⟨T,hTS,hTn,hcost,hExtra,hPoint,hClass,hPointRet,hLocal⟩ :=
    exists_retained_slice_counts I S (hSH.trans hHI) hSn point classes Qref HRef
      lambda (G*Cq) hlambda (mul_nonneg hG hCq) hretS lower hRatio
      (grainRelations grain Rel) (grainRelations_refl grain Rel hrefl)
      (grainRelations_symm grain Rel hsym) L hL
  have hGrain : HasUniformFibers T Q grain := by
    apply extra_relation_grain_uniformity T Q grain (grainRelations grain Rel) (Fin.natAdd d (0:Fin 1))
      (fun x y => ?_) (hExtra (Fin.natAdd d (0:Fin 1)))
    simp only [grainRelations,Fin.addCases_right]
  refine ⟨T,hTS,hTn,hcost,?_,hPoint,hClass,hGrain,?_,?_,hPointRet,hLocal⟩
  · intro j x y hx hy
    simpa only [grainRelations,Fin.addCases_left] using hExtra (Fin.castAdd 1 j) x y hx hy
  · intro x y hx hy hxy
    exact hquotient x y (hTS hx) (hTS hy) hxy
  · intro g hg
    have hcostR : (S.card:ℝ) ≤ (F:ℝ)*T.card := by exact_mod_cast hcost
    exact retained_grain_density_two_stage H S T hSH hTS grain Q hGrain t Cq F hCq
      (Nat.cast_nonneg _) hgrain hquotientRet hcostR g hg

end NativeRetainedGrainDensityCore
