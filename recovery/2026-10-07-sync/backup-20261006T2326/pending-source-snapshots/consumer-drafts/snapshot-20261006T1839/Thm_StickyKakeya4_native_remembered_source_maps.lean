/- UNVERIFIED literal occurrence construction for the remembered-height source.
An intermediate shaded pair keeps one actual original witness. Forgetting
that witness never asserts that all its other antecedents share its height. -/
import Theorems.Thm_StickyKakeya4_native_intermediate_parent_population
import Theorems.Thm_StickyKakeya4_native_current_reference_readback
import Theorems.Thm_StickyKakeya4_native_finite_image_weighted_choice
import Theorems.Thm_StickyKakeya4_native_phase_height_key

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000
noncomputable section
namespace NativeRememberedSourceMaps
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeLocalParentSource NativeRelativeParentLabels
open NativeRelativeCoarseReadback NativeTranslatedGrainHeightOverlap
open NativeMatrixHeightWholePoint

/-- Literal intermediate shaded pair paired with its unchanged original
incidence witness; the two equalities name the actual old phase and shadow. -/
def occurrences {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (backbone : Finset (Fin n))
    (a : ℝ) (m b : ℕ) (p : Parent)
    (hp : (parentLabels D backbone a (2^m) p).Nonempty)
    (Q : Finset Parent) (cells : Fin Q.card → Finset Index)
    (A : Finset (Fin n × Index)) : Finset ((Fin Q.card × Index) × (Fin n × Index)) :=
  ((incidences cells).product A).filter (fun z =>
    NativeCoarseCellSource.parentIndex Q z.1.1=relativeLabel D a (2^m) p (2^b) z.2.1 ∧
    z.1.2=(doublePair h backbone a m p hp (2^b) z.2).2)

lemma mem_occurrences {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (backbone : Finset (Fin n))
    (a : ℝ) (m b : ℕ) (p : Parent)
    (hp : (parentLabels D backbone a (2^m) p).Nonempty)
    (Q : Finset Parent) (cells : Fin Q.card → Finset Index)
    (A : Finset (Fin n × Index)) (z : (Fin Q.card × Index) × (Fin n × Index)) :
    z∈occurrences h backbone a m b p hp Q cells A ↔
      z.1∈incidences cells ∧ z.2∈A ∧
      NativeCoarseCellSource.parentIndex Q z.1.1=relativeLabel D a (2^m) p (2^b) z.2.1 ∧
      z.1.2=(doublePair h backbone a m p hp (2^b) z.2).2 := by
  simp only [occurrences,mem_filter,mem_product]
  tauto

/-- Original translated height and the actual FINAL local pair. -/
def taggedKey {n nA : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (C : FiniteScaleSource nA) (c : ℕ) (pA : Parent)
    (z : (Fin nA × Index) × (Fin n × Index)) : ℤ × (Fin nA × Index) :=
  (translatedHeight D a m z.2.2,NativeLocalCellCoherence.localPair C 0 (2^c) pA z.1)

def finalTime {nA : ℕ} (v : ℤ × (Fin nA × Index)) : ℤ := v.2.2 (3:Fin 4)

def selectedOccurrences {n nA : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (C : FiniteScaleSource nA) (c : ℕ) (pA : Parent)
    (O : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index))) := O.filter (fun z => taggedKey D a m C c pA z∈B)

def selectedPairs {n nA : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (C : FiniteScaleSource nA) (c : ℕ) (pA : Parent)
    (O : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index))) : Finset (Fin nA × Index) :=
  (selectedOccurrences D a m C c pA O B).image Prod.fst

/-- The remembered tagged image is exact after lifting back to occurrences. -/
theorem selected_tagged_image {n nA : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (C : FiniteScaleSource nA) (c : ℕ) (pA : Parent)
    (O : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index))) (hB : B⊆O.image (taggedKey D a m C c pA)) :
    (selectedOccurrences D a m C c pA O B).image (taggedKey D a m C c pA)=B := by
  ext v
  simp only [selectedOccurrences,mem_image,mem_filter]
  constructor
  · rintro ⟨z,⟨_hz,hzB⟩,rfl⟩
    exact hzB
  · intro hv
    obtain ⟨z,hz,rfl⟩ := mem_image.mp (hB hv)
    exact ⟨z,⟨hz,hv⟩,rfl⟩

/-- The literal final local-pair image is the tag-forgetting image of B.
No single-valued inverse from an intermediate shaded pair is claimed. -/
theorem selected_final_image {n nA : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (C : FiniteScaleSource nA) (c : ℕ) (pA : Parent)
    (O : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index))) (hB : B⊆O.image (taggedKey D a m C c pA)) :
    (selectedPairs D a m C c pA O B).image (NativeLocalCellCoherence.localPair C 0 (2^c) pA)=
      B.image Prod.snd := by
  rw [←selected_tagged_image D a m C c pA O B hB]
  simp only [selectedPairs,image_image]
  rfl

/-- Once one old height has been selected per final time label, forgetting
that height is injective on the retained tagged pairs. -/
theorem final_image_card {nA : ℕ} (B : Finset (ℤ × (Fin nA × Index)))
    (hcoherent : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1) :
    (B.image Prod.snd).card=B.card := by
  apply card_image_iff.mpr
  intro v hv w hw he
  exact Prod.ext (hcoherent v hv w hw (congrArg (fun p : Fin nA × Index => p.2 (3:Fin 4)) he)) he

/-- Every retained actual intermediate pair has a surviving original
witness. The old-height conclusion concerns this witness alone. -/
theorem selected_pair_witness {n nA : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (C : FiniteScaleSource nA) (c : ℕ) (pA : Parent)
    (O : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index))) (v : Fin nA × Index)
    (hv : v∈selectedPairs D a m C c pA O B) :
    ∃z : Fin n × Index,(v,z)∈O ∧
      (translatedHeight D a m z.2,NativeLocalCellCoherence.localPair C 0 (2^c) pA v)∈B := by
  obtain ⟨z,hz,he⟩ := mem_image.mp hv
  obtain ⟨hzO,hzB⟩ := mem_filter.mp hz
  subst v
  exact ⟨z.2,hzO,hzB⟩

/-- Apply the existing weighted choice to the actual tagged final image.
The parent geometry supplies the old-height count in each final time cell;
there is no output point-count hypothesis. The real bound is floored. -/
theorem select_old_height {n nA : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (C : FiniteScaleSource nA) (c : ℕ) (pA : Parent)
    (O : Finset ((Fin nA × Index) × (Fin n × Index))) {K : ℝ} (hK : 0 ≤ K)
    (hCard : ∀j,
      ((((O.image (taggedKey D a m C c pA)).filter (fun v => finalTime v=j)).image Prod.fst).card:ℝ) ≤ K) :
    ∃B⊆O.image (taggedKey D a m C c pA),
      ((O.image (taggedKey D a m C c pA)).card:ℝ) ≤
        K*((selectedPairs D a m C c pA O B).image
          (NativeLocalCellCoherence.localPair C 0 (2^c) pA)).card ∧
      (∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1) ∧
      (selectedPairs D a m C c pA O B).image (NativeLocalCellCoherence.localPair C 0 (2^c) pA)=
        B.image Prod.snd := by
  let S := O.image (taggedKey D a m C c pA)
  have hNat (j : ℤ) : ((S.filter (fun v => finalTime v=j)).image Prod.fst).card ≤ ⌊K⌋₊ :=
    (Nat.le_floor_iff hK).mpr (hCard j)
  obtain ⟨B,hBS,hret,_hImage,_hLocal,hCoherent⟩ :=
    NativeFiniteImageWeightedChoice.select_per_cell S (fun _ => 1) finalTime Prod.fst ⌊K⌋₊ hNat
  have hrNat : S.card ≤ ⌊K⌋₊*B.card := by simpa [mass] using hret
  have hr : (S.card:ℝ) ≤ (⌊K⌋₊:ℝ)*(B.card:ℝ) := by exact_mod_cast hrNat
  have he := selected_final_image D a m C c pA O B hBS
  refine ⟨B,hBS,?_,hCoherent,he⟩
  rw [he,final_image_card B hCoherent]
  exact hr.trans (mul_le_mul_of_nonneg_right (Nat.floor_le hK) (Nat.cast_nonneg _))

/-- The selector's integer-height count is exactly the configured physical
height count on every later occurrence fiber. Hsingle is restricted from the
unchanged baseline T, and finalTime injectivity is used in both directions. -/
theorem tagged_height_card_eq_physical {n nA : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (C : FiniteScaleSource nA) (c : ℕ) (pA p : Parent)
    (T : Finset (Fin n × Index))
    (O : Finset ((Fin nA × Index) × (Fin n × Index)))
    (hOT : ∀z∈O,z.2∈T)
    (s : CanonicalConfiguredE4Bridge.Split) (P : Submodule ℝ E4) (hP : P≤NativeHorizontalGrainSlice.heightKernel)
    (hd : Module.finrank ℝ P=CanonicalConfiguredE4Bridge.tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (CanonicalConfiguredE4Bridge.normalDim s))
      (Fin (CanonicalConfiguredE4Bridge.tangentDim s)) ℝ)
    (R0 : ℕ) (hR0 : 0 < R0)
    (Hsingle : ∀x∈T,∀y∈T,translatedHeight D a m x.2/((8*R0:ℕ):ℤ)=
      translatedHeight D a m y.2/((8*R0:ℕ):ℤ) → translatedHeight D a m x.2=translatedHeight D a m y.2)
    (j : ℤ) :
    (((O.image (taggedKey D a m C c pA)).filter (fun v => finalTime v=j)).image Prod.fst).card =
      ((O.filter (fun z => finalTime (taggedKey D a m C c pA z)=j)).image
        (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2.2 (3:Fin 4))).card := by
  let V := O.filter (fun z => finalTime (taggedKey D a m C c pA z)=j)
  let U := V.image Prod.snd
  have hUT : U⊆T := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hz
    exact hOT v (mem_filter.mp hv).1
  have hleft : ((O.image (taggedKey D a m C c pA)).filter (fun v => finalTime v=j)).image Prod.fst =
      U.image (fun z => translatedHeight D a m z.2) := by
    rw [filter_image,image_image]
    dsimp only [U,V]
    rw [image_image]
    rfl
  have hright : U.image (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2 (3:Fin 4)) =
      V.image (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2.2 (3:Fin 4)) := by
    rw [U,image_image]
    rfl
  rw [hleft,←hright]
  exact NativePhaseHeightKey.old_height_card_eq_physical (D:=D) (a:=a) (m:=m) (p:=p)
    (s:=s) (P:=P) (hP:=hP) (hd:=hd) (F:=F) (Fcfg:=Fcfg) (R:=R0) (U:=U) hR0
    (fun x hx y hy he => Hsingle x (hUT hx) y (hUT hy) he)


end NativeRememberedSourceMaps
