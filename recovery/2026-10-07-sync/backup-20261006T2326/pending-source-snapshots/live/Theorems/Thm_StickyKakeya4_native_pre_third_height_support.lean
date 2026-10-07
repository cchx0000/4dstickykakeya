import Theorems.Thm_StickyKakeya4_native_translated_height_freeze
import Theorems.Thm_StickyKakeya4_native_actual_configured_cell_selection
import Theorems.Thm_StickyKakeya4_native_actual_configured_residue

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
noncomputable section
namespace NativePreThirdHeightSupport
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeMatrixHeightWholePoint NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightMetric
open NativeTranslatedHeightFreeze NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeNormalizedCellRelativeMenu CanonicalConfiguredE4Bridge
open scoped Matrix.Norms.Elementwise

/-- The support selector uses a cell eight times wider than the final
working cell. The precise dyadic nesting gives the required implication. -/
lemma configured_fine_to_support (delta : ℝ) (x y : E4)
    (h : wzDyadicCellIndex (delta/512) x=wzDyadicCellIndex (delta/512) y) :
    wzDyadicCellIndex (delta/64) x=wzDyadicCellIndex (delta/64) y := by
  ext j
  have hj : ⌊x j/(delta/512)⌋=⌊y j/(delta/512)⌋ := congrFun h j
  have hh:=NativeFrozenTimeField.same_base_same_coarse 8 hj
  have he : (delta/512)*(8:ℝ)=delta/64 := by ring
  simpa only [Nat.cast_ofNat,he] using hh

/-- The actual two remaining pre-third cuts. The fields are frozen from the
single-height source once, and then the certified original-coordinate support
selector acts on that same source. A final GLOBAL residue8 cut supplies
both point separation and height separation with its same color witness.
Both the original wider support-cell implication and its finer nested
version are retained on the same final U. The literal single-old-height
property is retained for every later subset as well. Every whole-point cost is explicit. -/
theorem select_actual_height_support {n K : ℕ} {V : Type*} [Zero V]
    {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : 6≤ m) (p : Parent)
    (S : Finset (Fin n × Index)) (hS : S.Nonempty)
    (hparent : ∀z∈S,parentLabel D a (2^m) z.1=p)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤ heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (G : ℤ → V) (hF : ∀t,‖F t‖≤ (1/4:ℝ))
    (R0 : ℕ) (hR0 : 0< R0) (hbase : rho m≤ mu m*(R0:ℝ))
    (M J : Fin K → ℕ) (hM : ∀j,0< M j)
    (hmenu : ∀j,mu m*(R0:ℝ)≤ 64/(M j:ℝ))
    (hIntegral : ∀j,64/(M j:ℝ)=(mu m*(R0:ℝ))*(J j:ℝ)) :
    ∃Bh⊆S.image Prod.snd,let Sh:=edgeLift S Prod.snd Bh
    let Fcfg:=frozen D a m R0 Sh F
    let Gcfg:=frozen D a m R0 Sh G
    (∀t,‖Fcfg t‖≤ (1/4:ℝ)) ∧
    ∃B0⊆Sh.image Prod.snd,let U0:=edgeLift Sh Prod.snd B0
    ∃color : Fin 4 → Fin 8,∃B⊆U0.image Prod.snd,let U:=edgeLift U0 Prod.snd B
      U.Nonempty ∧ U⊆S ∧ S.card≤ (((8*R0)*53^(4*K))*8^4)*U.card ∧
      (∀k∈B,U.filter (fun z => z.2=k)=S.filter (fun z => z.2=k)) ∧
      (∀z∈U,Fcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ))=F (translatedHeight D a m z.2) ∧
        Gcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ))=G (translatedHeight D a m z.2)) ∧
      (∀j,∀x∈U,∀y∈U,
        wzDyadicCellIndex ((64/(M j:ℝ))/512)
          (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 x.2)=
        wzDyadicCellIndex ((64/(M j:ℝ))/512)
          (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 y.2) →
        physicalCell D a (2^m) (M j) p x.2=physicalCell D a (2^m) (M j) p y.2) ∧
      (∀j x y,
        ⌊NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 x (3:Fin 4)/((64/(M j:ℝ))/512)⌋=
        ⌊NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 y (3:Fin 4)/((64/(M j:ℝ))/512)⌋ →
        physicalCell D a (2^m) (M j) p x (3:Fin 4)=physicalCell D a (2^m) (M j) p y (3:Fin 4)) ∧
      (∀k∈B,SeparatedAlignmentPatches.color 8 (by norm_num)
        (NativeActualConfiguredResidue.parameter s (mu m) R0 F Fcfg
          (NativeActualConfiguredPoint.sourceLabel D a m p s P hP hd F k))=color) ∧
      (∀x∈U.image (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2),
        ∀y∈U.image (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2),
        x≠y → (mu m*(R0:ℝ))/64≤ dist x y) ∧
      (∀z∈U,∀u∈U,
        NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2 (3:Fin 4)≠
          NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 u.2 (3:Fin 4) →
        (mu m*(R0:ℝ))/64≤ dist
          (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2 (3:Fin 4))
          (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 u.2 (3:Fin 4))) ∧
      (∀j,∀x∈U,∀y∈U,
        wzDyadicCellIndex ((64/(M j:ℝ))/64)
          (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 x.2)=
        wzDyadicCellIndex ((64/(M j:ℝ))/64)
          (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 y.2) →
        physicalCell D a (2^m) (M j) p x.2=physicalCell D a (2^m) (M j) p y.2) ∧
      (∀T⊆U,∀z∈T,∀w∈T,
        translatedHeight D a m z.2/((8*R0:ℕ):ℤ)=translatedHeight D a m w.2/((8*R0:ℕ):ℤ) →
        translatedHeight D a m z.2=translatedHeight D a m w.2) := by
  obtain ⟨Bh,hBh,hSh,hShS,hHeightCost,hHeightFiber,hHeight,hFrozen⟩:=
    select_and_freeze D a m S hS F G R0 hR0
  let Sh:=edgeLift S Prod.snd Bh
  let Fcfg:=frozen D a m R0 Sh F
  have hCfg (t : ℤ) : ‖Fcfg t‖≤ (1/4:ℝ) := by
    exact NativeFrozenTimeField.field_norm_le Sh
      (fun z => referenceHeight m (translatedHeight D a m z.2))
      (fun z => F (translatedHeight D a m z.2)) (mu m*(R0:ℝ)) (1/4:ℝ)
      (by norm_num) (fun z _ => hF (translatedHeight D a m z.2)) t
  obtain ⟨B0,hB0,hU0Sh,hSupportCost,hSupportFiber,hSupport⟩:=
    NativeActualConfiguredCellSelection.select_actual_edges h m hm p Sh
      (fun z hz => hparent z (hShS hz)) s P hP hd F Fcfg hF hCfg R0 hR0 hbase K M hM hmenu
  let U0:=edgeLift Sh Prod.snd B0
  have hU0 : U0.Nonempty := by
    by_contra hn
    have hz : U0.card=0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hn)
    change Sh.card≤ 53^(4*K)*U0.card at hSupportCost
    rw [hz,mul_zero] at hSupportCost
    have hp:=card_pos.mpr hSh
    omega
  have hBhPoint (k : Index) (hk : k∈Sh.image Prod.snd) : k∈Bh := by
    obtain ⟨z,hz,rfl⟩:=mem_image.mp hk
    exact (mem_filter.mp hz).2
  obtain ⟨color,B,hB,hUU0,hResidueCost,hResidueFiber,hColor,hSep,hTimeSep⟩:=
    NativeActualConfiguredResidue.select_actual_edges D a m p U0 s P hP hd F Fcfg R0 hR0
  let U:=edgeLift U0 Prod.snd B
  have hU : U.Nonempty := by
    by_contra hn
    have hz : U.card=0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hn)
    change U0.card≤ 8^4*U.card at hResidueCost
    rw [hz,mul_zero] at hResidueCost
    have hp:=card_pos.mpr hU0
    omega
  have hUSh : U⊆Sh := hUU0.trans hU0Sh
  have hBPoint (k : Index) (hk : k∈B) : k∈B0 := by
    obtain ⟨z,hz,rfl⟩:=mem_image.mp (hB hk)
    exact (mem_filter.mp hz).2
  refine ⟨Bh,hBh,hCfg,B0,hB0,color,B,hB,hU,hUSh.trans hShS,?_,?_,?_,?_,?_,hColor,hSep,hTimeSep,?_,?_⟩
  · calc
      S.card≤ (8*R0)*Sh.card := hHeightCost
      _≤ (8*R0)*(53^(4*K)*U0.card) := Nat.mul_le_mul_left _ hSupportCost
      _=((8*R0)*53^(4*K))*U0.card := by ring
      _≤ ((8*R0)*53^(4*K))*(8^4*U.card) := Nat.mul_le_mul_left _ hResidueCost
      _=(((8*R0)*53^(4*K))*8^4)*U.card := by ring
  · intro k hk
    exact (hResidueFiber k hk).trans ((hSupportFiber k (hBPoint k hk)).trans
      (hHeightFiber k (hBhPoint k (hB0 (hBPoint k hk)))))
  · intro z hz
    exact hFrozen U hUSh z hz
  · intro j x hx y hy hcell
    exact hSupport j x (hUU0 hx) y (hUU0 hy) (configured_fine_to_support (64/(M j:ℝ)) _ _ hcell)
  · intro j x y htime
    have hs : 512*((64/(M j:ℝ))/512)=(mu m*(R0:ℝ))*(J j:ℝ) := by
      calc
        _=64/(M j:ℝ) := by ring
        _=(mu m*(R0:ℝ))*(J j:ℝ) := hIntegral j
    rw [NativeActualConfiguredPoint.point_height_floor D a m p s P hP hd F Fcfg R0 hR0 x _ (J j) hs,
      NativeActualConfiguredPoint.point_height_floor D a m p s P hP hd F Fcfg R0 hR0 y _ (J j) hs] at htime
    have he : 512*((64/(M j:ℝ))/512)=64/(M j:ℝ) := by ring
    rw [he] at htime
    exact htime
  · intro j x hx y hy hcell
    exact hSupport j x (hUU0 hx) y (hUU0 hy) hcell
  · intro T hTU z hz w hw he
    exact hHeight z (hUSh (hTU hz)) w (hUSh (hTU hw)) he

end NativePreThirdHeightSupport
