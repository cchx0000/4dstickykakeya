/- UNVERIFIED actual post-Y weighted joint cleanup. The only uniformity
is that of the reference T pair fibers, before the post-Y selection. -/
import Theorems.Thm_StickyKakeya4_native_joint_key_descent
import Theorems.Thm_StickyKakeya4_native_automatic_weighted_grain_core

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeWeightedJointCleanup
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeConfiguredThirdRelation NativeConfiguredJointRelation NativeJointKeyDescent
open CanonicalConfiguredE4Bridge NativeHorizontalGrainSlice NativeNormalizedCellRelativeMenu
open NativeJointUniformCoarseRelations NativeFiniteSliceHomogeneity
open NativeAutomaticWeightedGrainCore WeightedRichDirectionalLayers RichDirectionalLayers
open scoped BigOperators

/-- Apply the existing weighted deletion operator to actual deduplicated
pairs, with each weight equal to its full original T fiber. The resulting
cut retains half the selected original mass and keeps whole pair fibers.
Richness is converted to DISTINCT pair counts using reference pair HU;
no joint uniformity or X-density is asserted after this cut. -/
theorem exists_actual_rich_joint_core {n J : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (p : Parent) (split : Split)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim split)
    (F Fcfg : ℤ → Matrix (Fin (normalDim split)) (Fin (tangentDim split)) ℝ)
    (R u : ℕ) (hR : 0 < R) (depths : Fin J → ℕ)
    (hJ : 0 < J) (hdepths : ∀ j, depths j ≤ u+3)
    (U T : Finset (Fin n × Index)) (hTU : T ⊆ U)
    (Hbase : ∀ x ∈ U, ∀ y ∈ U,
      NativeActualConfiguredPoint.point D a m p split P hP hd F Fcfg R x.2 =
        NativeActualConfiguredPoint.point D a m p split P hP hd F Fcfg R y.2 →
      physicalCell D a (2^m) (2^(u+6)) p x.2 =
        physicalCell D a (2^m) (2^(u+6)) p y.2)
    (Q : ℕ)
    (HP : HasUniformFibers T Q (geometricPairKey D a m p split P hP hd F Fcfg R u))
    (A : Finset (Parent × E4))
    (hAG : A ⊆ T.image (geometricPairKey D a m p split P hP hd F Fcfg R u))
    (hAn : A.Nonempty) :
    let pair := geometricPairKey D a m p split P hP hd F Fcfg R u
    let G := T.image pair
    let w := fun z => (T.filter (fun x => pair x=z)).card
    let cls := fun j => onPair D a m p split P hP hd F Fcfg R u (depths j) U
    ∃ B ⊆ A, B.Nonempty ∧
      let kept := T.filter (fun x => pair x ∈ B)
      mass A w ≤ 2*kept.card ∧ kept.image pair=B ∧
      (∀ x ∈ kept, kept.filter (fun z => pair z=pair x)=T.filter (fun z => pair z=pair x)) ∧
      (∀ j, ∀ x ∈ kept, cls j (pair x)=jointKey D a m p R (depths j) x) ∧
      ∀ j, ∀ c ∈ B.image (cls j),
        (mass A w : ℝ)*(G.card:ℝ) <
          2*(J:ℝ)*((A.image (cls j)).card:ℝ)*(Q:ℝ)^2*(T.card:ℝ)*
            ((classFiber B (cls j) c).card:ℝ) := by
  intro pair G w cls
  have hGn : G.Nonempty := hAn.mono hAG
  have hmass : 0 < mass A w := by
    obtain ⟨z,hz⟩ := hAn
    have hw : 0 < w z := by
      obtain ⟨x,hx,he⟩ := mem_image.mp (hAG hz)
      exact card_pos.mpr ⟨x,mem_filter.mpr ⟨hx,he⟩⟩
    exact hw.trans_le (single_le_sum (fun _ _ => Nat.zero_le _) hz)
  obtain ⟨B,hBA,hBn,hhalf,_hloss,hrich⟩ :=
    exists_automatic_simultaneous_dense_core hJ A cls w hmass
  let kept := T.filter (fun x => pair x ∈ B)
  have hBG : B ⊆ G := hBA.trans hAG
  have hmassB : mass B w = kept.card :=
    sum_card_fiberwise_eq_card_filter T B pair
  have himage : kept.image pair = B := by
    ext z
    constructor
    · rintro hz
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
      exact (mem_filter.mp hx).2
    · intro hz
      obtain ⟨x,hx,he⟩ := mem_image.mp (hBG hz)
      exact mem_image.mpr ⟨x,mem_filter.mpr ⟨hx,by simpa only [he] using hz⟩,he⟩
  refine ⟨B,hBA,hBn,?_,himage,?_,?_,?_⟩
  · simpa only [hmassB] using hhalf
  · intro x hx
    have hBx := (mem_filter.mp hx).2
    ext z
    simp only [kept,mem_filter]
    constructor
    · exact fun hz => ⟨hz.1.1,hz.2⟩
    · rintro ⟨hz,he⟩
      exact ⟨⟨hz,by simpa only [he] using hBx⟩,he⟩
  · intro j x hx
    exact onPair_readback D a m p split P hP hd F Fcfg R u (depths j)
      hR (hdepths j) U Hbase x (hTU (mem_filter.mp hx).1)
  · intro j c hc
    let C := classFiber B (cls j) c
    have hCG : C ⊆ G := (filter_subset _ _).trans hBG
    have hwbound (z : Parent × E4) (hz : z ∈ G) : w z*G.card ≤ Q^2*T.card :=
      (fiber_card_average_cross T pair (Q^2) HP z hz).1
    have hcap : mass C w*G.card ≤ Q^2*T.card*C.card := by
      calc
        _ = ∑ z ∈ C,w z*G.card := by simp only [mass,sum_mul]
        _ ≤ ∑ _z ∈ C,Q^2*T.card := sum_le_sum (fun z hz => hwbound z (hCG hz))
        _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring
    have hcapR : (mass C w:ℝ)*(G.card:ℝ) ≤ (Q:ℝ)^2*(T.card:ℝ)*(C.card:ℝ) := by
      exact_mod_cast hcap
    have hAc : 0 < (A.image (cls j)).card := card_pos.mpr ⟨c,(image_subset_image hBA) hc⟩
    have hden : (0:ℝ) < 2*(J:ℝ)*((A.image (cls j)).card:ℝ) := by
      have hjr : (0:ℝ) < J := by exact_mod_cast hJ
      have hcr : (0:ℝ) < (A.image (cls j)).card := by exact_mod_cast hAc
      positivity
    have hr : (mass A w:ℝ) <
        (2*(J:ℝ)*((A.image (cls j)).card:ℝ))*(mass C w:ℝ) := by
      simpa only [mul_comm] using (div_lt_iff₀ hden).mp (hrich j c hc).2
    have hGr : (0:ℝ) < G.card := by exact_mod_cast card_pos.mpr hGn
    calc
      _ < ((2*(J:ℝ)*((A.image (cls j)).card:ℝ))*(mass C w:ℝ))*(G.card:ℝ) :=
        mul_lt_mul_of_pos_right hr hGr
      _ = (2*(J:ℝ)*((A.image (cls j)).card:ℝ))*((mass C w:ℝ)*(G.card:ℝ)) := by ring
      _ ≤ (2*(J:ℝ)*((A.image (cls j)).card:ℝ))*((Q:ℝ)^2*(T.card:ℝ)*(C.card:ℝ)) :=
        mul_le_mul_of_nonneg_left hcapR hden.le
      _ = _ := by ring

end NativeWeightedJointCleanup
