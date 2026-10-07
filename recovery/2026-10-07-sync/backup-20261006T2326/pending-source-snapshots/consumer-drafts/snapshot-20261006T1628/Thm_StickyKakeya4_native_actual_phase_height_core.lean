/- UNVERIFIED phase-only actual source operator. No spatial menu or
new self-uniform refinement is used. Population is read from the same HB. -/
import Theorems.Thm_StickyKakeya4_native_weighted_phase_height_core
import Theorems.Thm_StickyKakeya4_native_actual_phase_height_population

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeActualPhaseHeightCore
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeConfiguredThirdRelation NativePhaseHeightKey NativeActualPhaseHeightPopulation
open NativeWeightedPhaseHeightCore NativeHorizontalGrainSlice CanonicalConfiguredE4Bridge
open NativeJointUniformCoarseRelations NativeLocalParentSource NativeTranslatedGrainHeightOverlap
open WeightedRichDirectionalLayers RichDirectionalLayers SelfUniform

/-- The actual third caller supplies reference pair weights. Original HB
supplies the complete phase count. Their weighted phase/old-height cleanup
then chooses a massive parent with a rich class at EVERY occupied old height.
All lower bounds count literal geometric pairs, preserving original witnesses. -/
theorem from_original_reference {n d : ℕ} {D : FiniteScaleSource n}
    {eta localEta a zeta profile : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (Rfull : Finset (Fin n)) (level : ℕ) (hzeta : 0 ≤ zeta)
    (HB : NativeMiddleWindowBalance.HasOriginalBackbone D original Rfull a level zeta)
    (Eref : Finset (Fin n × Index)) (m c : ℕ) (hm : m ≤ level) (hc : c ≤ level-m+6)
    (p : Parent) (href : IsWangZakharovNativeFiniteInput (source h Rfull Eref a m p) localEta)
    (hbudget : (64:ℝ)^3*(source h Rfull Eref a m p).thickness^profile ≤ D.thickness^zeta)
    (T : Finset (Fin n × Index)) (hParent : ∀z∈T,z.1∈parentLabels D Rfull a (2^m) p)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R u : ℕ) (hR : 0 < R) (hcu : c ≤ u+12)
    (Hsingle : ∀x∈T,∀y∈T,translatedHeight D a m x.2/((8*R:ℕ):ℤ)=
      translatedHeight D a m y.2/((8*R:ℕ):ℤ) → translatedHeight D a m x.2=translatedHeight D a m y.2)
    (Q : ℕ) (extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (Hcaller : ∀j x y,x∈T → y∈T →
      degree (fun _ : Fin n × Index => 1) (completeRelations D a m p s P hP hd F Fcfg R u extra j) T x ≤
      Q^2*degree (fun _ : Fin n × Index => 1) (completeRelations D a m p s P hP hd F Fcfg R u extra j) T y)
    (A : Finset (Parent × E4))
    (hAG : A⊆T.image (geometricPairKey D a m p s P hP hd F Fcfg R u)) (hAn : A.Nonempty) :
    let pair := geometricPairKey D a m p s P hP hd F Fcfg R u
    let G := T.image pair
    let Z := T.image (fun z => translatedHeight D a m z.2)
    let weight := fun v => (T.filter (fun z => pair z=v)).card
    let cls := onPair D a m p s P hP hd F Fcfg R u c T
    let phaseCap := 373248*(source h Rfull Eref a m p).thickness^(-profile)*(((2^c:ℕ):ℝ))^3
    ∃B⊆A,B.Nonempty ∧ mass A weight ≤ 2*mass B weight ∧
      ∃parent∈B.image (fun v => (cls v).2),
      let Bparent := B.filter (fun v => (cls v).2=parent)
      Bparent.Nonempty ∧
      (mass A weight:ℝ)*(G.card:ℝ) ≤ 2*phaseCap*(Q:ℝ)^2*(T.card:ℝ)*(Bparent.card:ℝ) ∧
      (∀height∈Bparent.image (fun v => (cls v).1),
        (mass A weight:ℝ)*(G.card:ℝ) <
          2*(Z.card:ℝ)*phaseCap*(Q:ℝ)^2*(T.card:ℝ)*
            ((Bparent.filter (fun v => (cls v).1=height)).card:ℝ)) ∧
      (∀v∈Bparent,∃z∈T,pair z=v ∧ translatedHeight D a m z.2=(cls v).1 ∧
        NativeRelativeParentLabels.relativeLabel D a (2^m) p (2^c) z.1=parent) ∧
      let Eparent := T.filter (fun z => pair z∈Bparent)
      Eparent.image pair=Bparent ∧
        ∀x∈Eparent,Eparent.filter (fun z => pair z=pair x)=T.filter (fun z => pair z=pair x) := by
  intro pair G Z weight cls phaseCap
  let Sref := source h Rfull Eref a m p
  let allParents := (univ : Finset (Fin (parentLabels D Rfull a (2^m) p).card)).image
    (parentLabel Sref 0 (2^c))
  have hCap : (allParents.card:ℝ) ≤ phaseCap :=
    actual_full_phase_card h original Rfull level hzeta HB Eref m c hm hc p href hbudget
  have hread (v : Parent × E4) (hv : v∈A) :
      ∃z∈T,pair z=v ∧ cls v=originalKey D a m c p z := by
    obtain ⟨z,hz,he⟩ := mem_image.mp (hAG hv)
    refine ⟨z,hz,he,?_⟩
    rw [←he]
    exact onPair_readback D a m p s P hP hd F Fcfg R u c T hR hcu Hsingle z hz
  have hphases : A.image (fun v => (cls v).2)⊆allParents := by
    intro q hq
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hq
    obtain ⟨z,hz,_he,hr⟩ := hread v hv
    rw [hr]
    exact relative_parent_mem_full h Rfull Eref a m c p z.1 (hParent z hz)
  have hkeys : A.image cls⊆Z.product allParents := by
    intro q hq
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hq
    obtain ⟨z,hz,_he,hr⟩ := hread v hv
    rw [hr]
    exact mem_product.mpr ⟨mem_image_of_mem _ hz,
      relative_parent_mem_full h Rfull Eref a m c p z.1 (hParent z hz)⟩
  have hphaseCard : ((A.image (fun v => (cls v).2)).card:ℝ) ≤ phaseCap :=
    (Nat.cast_le.mpr (card_le_card hphases)).trans hCap
  have hkeyCard : ((A.image cls).card:ℝ) ≤ (Z.card:ℝ)*phaseCap := by
    have hh : (A.image cls).card ≤ Z.card*allParents.card :=
      (card_le_card hkeys).trans_eq (card_product _ _)
    exact (show ((A.image cls).card:ℝ) ≤ (Z.card:ℝ)*(allParents.card:ℝ) by exact_mod_cast hh).trans
      (mul_le_mul_of_nonneg_left hCap (Nat.cast_nonneg _))
  have HP := caller_geometricPair_uniformity D a m p s P hP hd F Fcfg R u extra T Q Hcaller
  obtain ⟨B,hBA,hBn,hhalf,hWitness,hRich,parent,hparent,hParentN,_hBcard,hMassive,hClass,hImage,hFiber⟩ :=
    exists_actual_phase_core D a m p s P hP hd F Fcfg R u c hR hcu T Hsingle Q HP A hAG hAn
  let Bparent := B.filter (fun v => (cls v).2=parent)
  refine ⟨B,hBA,hBn,hhalf,parent,hparent,hParentN,?_,?_,?_,hImage,hFiber⟩
  · exact hMassive.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hphaseCard (by norm_num))
            (sq_nonneg (Q:ℝ))) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
  · intro height hh
    obtain ⟨v,hv,hvh⟩ := mem_image.mp hh
    have hclass : (height,parent)∈B.image cls := by
      exact mem_image.mpr ⟨v,(mem_filter.mp hv).1,
        Prod.ext hvh (mem_filter.mp hv).2⟩
    have hlower := hRich (height,parent) hclass
    rw [←hClass height hh] at hlower
    have hbound := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkeyCard (by norm_num : (0:ℝ) ≤ 2))
          (sq_nonneg (Q:ℝ))) (Nat.cast_nonneg T.card))
      (Nat.cast_nonneg (Bparent.filter (fun v => (cls v).1=height)).card)
    exact hlower.trans_le (by simpa only [mul_assoc] using hbound)
  · intro v hv
    obtain ⟨z,hz,he,hr⟩ := hWitness v (mem_filter.mp hv).1
    refine ⟨z,hz,he,?_,?_⟩
    · exact (congrArg Prod.fst hr).symm
    · exact (congrArg Prod.snd hr).symm.trans (mem_filter.mp hv).2

end NativeActualPhaseHeightCore
