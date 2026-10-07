/- UNVERIFIED actual phase-only weighted deletion and massive-parent choice. -/
import Theorems.Thm_StickyKakeya4_native_phase_height_key
import Theorems.Thm_StickyKakeya4_native_automatic_weighted_grain_core
import Theorems.Thm_StickyKakeya4_native_finite_slice_homogeneity

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000
noncomputable section
namespace NativeWeightedPhaseHeightCore
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeConfiguredThirdRelation NativePhaseHeightKey NativeHorizontalGrainSlice CanonicalConfiguredE4Bridge
open NativeJointUniformCoarseRelations NativeFiniteSliceHomogeneity
open NativeAutomaticWeightedGrainCore WeightedRichDirectionalLayers RichDirectionalLayers
open scoped BigOperators

/-- The map is exactly (original height, old phase parent). Original T pair
fibers give the actual weights. The automatic deletion keeps half the chosen
mass and makes every surviving height/parent class rich in DISTINCT pairs.
A massive phase parent is then chosen by its original edge weight. -/
theorem exists_actual_phase_core {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (p : Parent) (s : Split)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R u c : ℕ) (hR : 0 < R) (hc : c ≤ u+12) (T : Finset (Fin n × Index))
    (Hsingle : ∀x∈T,∀y∈T,NativeTranslatedGrainHeightOverlap.translatedHeight D a m x.2/((8*R:ℕ):ℤ)=
      NativeTranslatedGrainHeightOverlap.translatedHeight D a m y.2/((8*R:ℕ):ℤ) →
      NativeTranslatedGrainHeightOverlap.translatedHeight D a m x.2=
        NativeTranslatedGrainHeightOverlap.translatedHeight D a m y.2)
    (Q : ℕ) (HP : HasUniformFibers T Q (geometricPairKey D a m p s P hP hd F Fcfg R u))
    (A : Finset (Parent × E4))
    (hAG : A⊆T.image (geometricPairKey D a m p s P hP hd F Fcfg R u)) (hAn : A.Nonempty) :
    let pair := geometricPairKey D a m p s P hP hd F Fcfg R u
    let G := T.image pair
    let weight := fun v => (T.filter (fun z => pair z=v)).card
    let cls := onPair D a m p s P hP hd F Fcfg R u c T
    ∃B⊆A,B.Nonempty ∧
      mass A weight ≤ 2*mass B weight ∧
      (∀v∈B,∃z∈T,pair z=v ∧ cls v=originalKey D a m c p z) ∧
      (∀q∈B.image cls,(mass A weight:ℝ)*(G.card:ℝ) <
        2*((A.image cls).card:ℝ)*(Q:ℝ)^2*(T.card:ℝ)*((classFiber B cls q).card:ℝ)) ∧
      ∃parent∈B.image (fun v => (cls v).2),
        let Bparent := B.filter (fun v => (cls v).2=parent)
        Bparent.Nonempty ∧
        mass A weight ≤ 2*(A.image (fun v => (cls v).2)).card*mass Bparent weight ∧
        (mass A weight:ℝ)*(G.card:ℝ) ≤
          2*((A.image (fun v => (cls v).2)).card:ℝ)*(Q:ℝ)^2*(T.card:ℝ)*(Bparent.card:ℝ) ∧
        (∀height∈Bparent.image (fun v => (cls v).1),
          Bparent.filter (fun v => (cls v).1=height)=classFiber B cls (height,parent)) ∧
        let Eparent := T.filter (fun z => pair z∈Bparent)
        Eparent.image pair=Bparent ∧
          ∀x∈Eparent,Eparent.filter (fun z => pair z=pair x)=T.filter (fun z => pair z=pair x) := by
  intro pair G weight cls
  have hGn := hAn.mono hAG
  have hmass : 0 < mass A weight := by
    obtain ⟨v,hv⟩ := hAn
    obtain ⟨z,hz,he⟩ := mem_image.mp (hAG hv)
    have hw : 0 < weight v := card_pos.mpr ⟨z,mem_filter.mpr ⟨hz,he⟩⟩
    exact hw.trans_le (single_le_sum (fun _ _ => Nat.zero_le _) hv)
  obtain ⟨B,hBA,hBn,hhalf,_hloss,hrich⟩ :=
    exists_automatic_simultaneous_dense_core (J:=1) (by norm_num) A (fun _ => cls) weight hmass
  have hBG : B⊆G := hBA.trans hAG
  have hcap (C : Finset (Parent × E4)) (hCG : C⊆G) :
      (mass C weight:ℝ)*(G.card:ℝ) ≤ (Q:ℝ)^2*(T.card:ℝ)*(C.card:ℝ) := by
    have hh : mass C weight*G.card ≤ Q^2*T.card*C.card := by
      calc
        _ = ∑v∈C,weight v*G.card := by simp only [mass,sum_mul]
        _ ≤ ∑_v∈C,Q^2*T.card := sum_le_sum (fun v hv =>
          (fiber_card_average_cross T pair (Q^2) HP v (hCG hv)).1)
        _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring
    exact_mod_cast hh
  have hRich : ∀q∈B.image cls,(mass A weight:ℝ)*(G.card:ℝ) <
      2*((A.image cls).card:ℝ)*(Q:ℝ)^2*(T.card:ℝ)*((classFiber B cls q).card:ℝ) := by
    intro q hq
    have hnum : 0 < (A.image cls).card := card_pos.mpr ⟨q,image_subset_image hBA hq⟩
    have hden : (0:ℝ) < 2*((A.image cls).card:ℝ) := by exact_mod_cast (show 0 < 2*(A.image cls).card by omega)
    have hh := (hrich (0:Fin 1) q hq).2
    simp only [Nat.cast_one,mul_one] at hh
    have hcross := (div_lt_iff₀ hden).mp hh
    have hgp : (0:ℝ) < G.card := by exact_mod_cast hGn.card_pos
    have hf := hcap (classFiber B cls q) ((filter_subset _ _).trans hBG)
    calc
      _ < (2*((A.image cls).card:ℝ)*(mass (classFiber B cls q) weight:ℝ))*(G.card:ℝ) := by
        simpa only [mul_comm] using mul_lt_mul_of_pos_right hcross hgp
      _ = (2*((A.image cls).card:ℝ))*((mass (classFiber B cls q) weight:ℝ)*(G.card:ℝ)) := by ring
      _ ≤ (2*((A.image cls).card:ℝ))*((Q:ℝ)^2*(T.card:ℝ)*((classFiber B cls q).card:ℝ)) :=
        mul_le_mul_of_nonneg_left hf hden.le
      _ = _ := by ring
  let phases := B.image (fun v => (cls v).2)
  have hpn : phases.Nonempty := hBn.image _
  obtain ⟨parent,hparent,hmax⟩ := exists_max_image phases
    (fun q => mass (B.filter (fun v => (cls v).2=q)) weight) hpn
  let Bparent := B.filter (fun v => (cls v).2=parent)
  have hparentn : Bparent.Nonempty := by
    obtain ⟨v,hv,hvparent⟩ := mem_image.mp hparent
    exact ⟨v,mem_filter.mpr ⟨hv,hvparent⟩⟩
  have hBmass : mass B weight ≤ (A.image (fun v => (cls v).2)).card*mass Bparent weight := by
    have hh : mass B weight ≤ phases.card*mass Bparent weight := by
      calc
        _ = ∑q∈phases,mass (B.filter (fun v => (cls v).2=q)) weight :=
          (sum_fiberwise_of_maps_to (fun v hv => mem_image_of_mem (fun v => (cls v).2) hv) weight).symm
        _ ≤ ∑_q∈phases,mass Bparent weight := sum_le_sum (fun q hq => hmax q hq)
        _ = _ := by simp only [sum_const,nsmul_eq_mul]
    have hphase := card_le_card (image_subset_image (f:=fun v => (cls v).2) hBA)
    exact hh.trans (Nat.mul_le_mul_right (mass Bparent weight) hphase)
  have hparentmass : mass A weight ≤ 2*(A.image (fun v => (cls v).2)).card*mass Bparent weight :=
    hhalf.trans (by simpa only [mul_assoc] using Nat.mul_le_mul_left 2 hBmass)
  have hmassive : (mass A weight:ℝ)*(G.card:ℝ) ≤
      2*((A.image (fun v => (cls v).2)).card:ℝ)*(Q:ℝ)^2*(T.card:ℝ)*(Bparent.card:ℝ) := by
    have hh : (mass A weight:ℝ) ≤ 2*((A.image (fun v => (cls v).2)).card:ℝ)*(mass Bparent weight:ℝ) :=
      by exact_mod_cast hparentmass
    calc
      _ ≤ (2*((A.image (fun v => (cls v).2)).card:ℝ)*(mass Bparent weight:ℝ))*(G.card:ℝ) :=
        mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg _)
      _ = (2*((A.image (fun v => (cls v).2)).card:ℝ))*((mass Bparent weight:ℝ)*(G.card:ℝ)) := by ring
      _ ≤ (2*((A.image (fun v => (cls v).2)).card:ℝ))*
          ((Q:ℝ)^2*(T.card:ℝ)*(Bparent.card:ℝ)) :=
        mul_le_mul_of_nonneg_left (hcap Bparent ((filter_subset _ _).trans hBG)) (by positivity)
      _ = _ := by ring
  refine ⟨B,hBA,hBn,hhalf,?_,hRich,parent,hparent,hparentn,hparentmass,hmassive,?_,?_,?_⟩
  · intro v hv
    obtain ⟨z,hz,he⟩ := mem_image.mp (hBG hv)
    refine ⟨z,hz,he,?_⟩
    rw [←he]
    exact onPair_readback D a m p s P hP hd F Fcfg R u c T hR hc Hsingle z hz
  · intro height _hh
    ext v
    simp only [Bparent,classFiber,mem_filter,Prod.ext_iff]
    tauto
  · ext v
    constructor
    · rintro hv
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hv
      exact (mem_filter.mp hz).2
    · intro hv
      obtain ⟨z,hz,he⟩ := mem_image.mp (hBG (mem_filter.mp hv).1)
      exact mem_image.mpr ⟨z,mem_filter.mpr ⟨hz,by simpa only [he] using hv⟩,he⟩
  · intro x hx
    ext z
    simp only [mem_filter]
    constructor
    · exact fun hz => ⟨hz.1.1,hz.2⟩
    · rintro ⟨hz,he⟩
      exact ⟨⟨hz,by simpa only [he] using (mem_filter.mp hx).2⟩,he⟩

end NativeWeightedPhaseHeightCore
