/- UNVERIFIED consolidated remembered-source construction.
This staging file preserves the 36 declarations from the source units listed
in its adjacent recovery manifest. No source check or imported-axiom audit
has been run on this file. The source units remain recovery snapshots.
Only imports and anonymous section boundaries are consolidated. -/
import Theorems.Thm_StickyKakeya4_native_actual_fine_weight_shading_bridge
import Theorems.Thm_StickyKakeya4_native_configured_height_caps
import Theorems.Thm_StickyKakeya4_native_configured_output_pairs
import Theorems.Thm_StickyKakeya4_native_current_reference_readback
import Theorems.Thm_StickyKakeya4_native_finite_image_weighted_choice
import Theorems.Thm_StickyKakeya4_native_full_chart_tube_graph
import Theorems.Thm_StickyKakeya4_native_intermediate_parent_population
import Theorems.Thm_StickyKakeya4_native_joint_local_xy_geometry
import Theorems.Thm_StickyKakeya4_native_joint_spatial_geometry
import Theorems.Thm_StickyKakeya4_native_matched_shadow_configured_geometry
import Theorems.Thm_StickyKakeya4_native_original_phase_chart_gaps
import Theorems.Thm_StickyKakeya4_native_phase_height_key
import Theorems.Thm_StickyKakeya4_native_remembered_height_geometry
import Theorems.Thm_StickyKakeya4_native_same_Q_source_restriction
import Theorems.Thm_StickyKakeya4_native_third_XY_data

/- Source unit: native_remembered_source_maps
   Original SHA256: 2fd204c7be77230a83c6a2b82a2383e9443e775496567614823b2f18a864d724 -/
/- UNVERIFIED literal occurrence construction for the remembered-height source.
An intermediate shaded pair keeps one actual original witness. Forgetting
that witness never asserts that all its other antecedents share its height. -/

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
  simp only [occurrences,mem_filter]
  constructor
  · rintro ⟨hz,hphase,hshadow⟩
    obtain ⟨hv,hw⟩ := Finset.mem_product.mp hz
    exact ⟨hv,hw,hphase,hshadow⟩
  · rintro ⟨hv,hw,hphase,hshadow⟩
    exact ⟨Finset.mem_product.mpr ⟨hv,hw⟩,hphase,hshadow⟩

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
  calc
    _ = ((selectedOccurrences D a m C c pA O B).image
        (taggedKey D a m C c pA)).image Prod.snd := by
      simp only [selectedPairs,image_image,Function.comp_def,taggedKey]
    _ = _ := congrArg (fun S : Finset (ℤ × (Fin nA × Index)) => S.image Prod.snd)
      (selected_tagged_image D a m C c pA O B hB)

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
    dsimp only [U]
    rw [image_image]
    rfl
  rw [hleft,←hright]
  exact NativePhaseHeightKey.old_height_card_eq_physical (D:=D) (a:=a) (m:=m) (p:=p)
    (s:=s) (P:=P) (hP:=hP) (hd:=hd) (F:=F) (Fcfg:=Fcfg) (R:=R0) (U:=U) hR0
    (fun x hx y hy he => Hsingle x (hUT hx) y (hUT hy) he)


end NativeRememberedSourceMaps

end -- anonymous noncomputable section of native_remembered_source_maps

/- Source unit: native_remembered_cell_halo
   Original SHA256: b378e73c42b0a28cc99e2bf322ba0eabd8f6ef0371ad759801b9eb025eb77497 -/
/- UNVERIFIED geometric halo for literal remembered-source occurrences. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeRememberedCellHalo
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalCellChartGeometry NativeLocalParentSource NativeLocalParentCells
open NativeLocalParentPhysicalMap NativeLocalCellCoherence NativeRelativeCoarseReadback
open NativeMatchedShadowConfiguredGeometry NativeRememberedSourceMaps
open NativeReferenceXYGridPoints NativeHorizontalGrainSlice CanonicalConfiguredE4Bridge

/-- The actual parent map has its explicit N/64 Lipschitz bound. -/
theorem physical_map_dist {n : ℕ} {C : FiniteScaleSource n} {eta : ℝ}
    (hC : IsWangZakharovNativeFiniteInput C eta) (a : ℝ) (N : ℕ) (hN : 0 < N)
    (p : Parent) (i : Fin n) (hi : parentLabel C a N i=p) (x y : E4) :
    dist (physicalMap C a N p x) (physicalMap C a N p y) ≤ (N:ℝ)*dist x y/64 := by
  have hh := baseMap_dist_le N hN ((shift C a:ℝ)*mesh C) p
    (parent_slope_bound hC N hN p i hi) x y
  unfold physicalMap
  rw [NativeContractedUnitParent.contract_dist]
  have hdiv := div_le_div_of_nonneg_right hh (by norm_num : (0:ℝ) ≤ 32)
  simpa only [div_div,show (2:ℝ)*32=64 by norm_num] using hdiv

/-- Literal local-cell rounding costs at most2sigma in E4. It is derived
from the original native shading membership and the actual front map. -/
theorem local_center_near_map {n : ℕ} {C : FiniteScaleSource n} {eta : ℝ}
    (hC : IsWangZakharovNativeFiniteInput C eta) (cells : Fin n → Finset Index)
    (hcells : ∀i,C.shading i=wzCellShading (mesh C) cells i)
    (ha : ∀i,wzGraphTime (C.line i) 0-mark (C.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (i : Fin n) (k : Index) (hk : k∈cells i) :
    dist (cellCenter ((N:ℝ)*C.thickness/128) (localCellLabel C 0 N p (i,k)))
      (physicalMap C 0 N p (cellCenter (mesh C) k)) ≤ 2*((N:ℝ)*C.thickness/64) := by
  have he : 0 < (N:ℝ)*C.thickness/128 := by have hd := hC.1.2.1; positivity
  apply (distance_of_coordinates _ _ ((N:ℝ)*C.thickness/64) (by linarith only [he]) ?_)
  intro j
  have hr := NativeRelativeCoarseGeometry.cell_center_coordinate_error he (frontPoint C 0 N p i k) j
  have hf := frontPoint_near_physicalCell hC cells hcells ha N p i k hk j
  have htri := abs_sub_le
    (cellCenter ((N:ℝ)*C.thickness/128) (localCellLabel C 0 N p (i,k)) j)
    (frontPoint C 0 N p i k j) (physicalMap C 0 N p (cellCenter (mesh C) k) j)
  change |cellCenter ((N:ℝ)*C.thickness/128) (localCellLabel C 0 N p (i,k)) j-
    frontPoint C 0 N p i k j| ≤ _ at hr
  linarith only [hr,hf,htri]

/-- A genuine original occurrence supplies the2d intermediate shadow error.
The final local cell is consequently within4sigma of the common physical
image of its own original configured point. No halo certificate is assumed. -/
theorem occurrence_center_near {n : ℕ} {D : FiniteScaleSource n} {eta etaC a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (backbone : Finset (Fin n)) (m b : ℕ) (hm : 6 ≤ m) (p : Parent)
    (hp : (parentLabels D backbone a (2^m) p).Nonempty)
    (hNscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (hRelScale : ((2^m:ℕ):ℝ)*D.thickness*((2^b:ℕ):ℝ) ≤ 64)
    (Q : Finset Parent) (C : FiniteScaleSource Q.card)
    (hC : IsWangZakharovNativeFiniteInput C etaC)
    (cells : Fin Q.card → Finset Index)
    (hcells : ∀i,C.shading i=wzCellShading (mesh C) cells i)
    (haC : ∀i,wzGraphTime (C.line i) 0-mark (C.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (hthickness : C.thickness=64/((2^b:ℕ):ℝ))
    (A : Finset (Fin n × Index)) (hA : A⊆NativeCubicalIncidenceCounts.incidences original)
    (hparent : ∀z∈A,z.1∈parentLabels D backbone a (2^m) p)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀t i j,|F t i j| ≤ 1/4) (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ) ≤ 4096/((2^b:ℕ):ℝ))
    (c : ℕ) (pA : Parent)
    (z : (Fin Q.card × Index) × (Fin n × Index))
    (hz : z∈occurrences h backbone a m b p hp Q cells A)
    (hcurrent : parentLabel C 0 (2^c) z.1.1=pA) :
    let O := NativePackedFrameIsometry.frame s P hP hd
    let cfg := NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2.2
    dist (cellCenter (((2^c:ℕ):ℝ)*C.thickness/128)
        (localCellLabel C 0 (2^c) pA z.1))
      (physicalMap C 0 (2^c) pA (O.symm cfg)) ≤ 4*(((2^c:ℕ):ℝ)*C.thickness/64) := by
  intro O cfg
  obtain ⟨hzCells,hzA,_hphase,hshadow⟩ := (mem_occurrences h backbone a m b p hp Q cells A z).mp hz
  have horig : z.2.2∈original z.2.1 :=
    (NativeCubicalIncidenceCounts.mem_incidences original _ _).mp (hA hzA)
  have hi := (mem_parentLabels D backbone a (2^m) p _).mp (hparent z.2 hzA)
  let rep := originalRepresentative h backbone a m p hp (2^b)
    (NativeRelativeParentLabels.relativeLabel D a (2^m) p (2^b) z.2.1)
  have hr := originalRepresentative_label h backbone a m p hp (2^b) z.2.1 (hparent z.2 hzA)
  have hnear := point_shadow_center_distance h original horiginal ha m (2^b) hm (by positivity)
    hNscale hRelScale p z.2.1 rep z.2.2 horig hi.2 hr s P hP hd F Fcfg hF hCfg
    R0 hR0 hbase hmatch
  have hcenter : dist (cellCenter (mesh C) z.1.2) (O.symm cfg) ≤ 2*C.thickness := by
    rw [←O.dist_map,LinearIsometryEquiv.apply_symm_apply,dist_comm]
    change dist cfg (O (cellCenter (C.thickness/2) z.1.2)) ≤ _
    rw [hthickness,hshadow]
    have he : (64/((2^b:ℕ):ℝ))/2=32/((2^b:ℕ):ℝ) := by ring
    rw [he]
    exact hnear
  have hmap := physical_map_dist hC 0 (2^c) (by positivity) pA z.1.1 hcurrent
    (cellCenter (mesh C) z.1.2) (O.symm cfg)
  have hround := local_center_near_map hC cells hcells haC (2^c) (by positivity) pA z.1.1 z.1.2
    ((NativeCubicalIncidenceCounts.mem_incidences cells _ _).mp hzCells)
  have htri := dist_triangle
    (cellCenter (((2^c:ℕ):ℝ)*C.thickness/128) (localCellLabel C 0 (2^c) pA z.1))
    (physicalMap C 0 (2^c) pA (cellCenter (mesh C) z.1.2))
    (physicalMap C 0 (2^c) pA (O.symm cfg))
  have hb := mul_le_mul_of_nonneg_left hcenter (show (0:ℝ) ≤ ((2^c:ℕ):ℝ) by positivity)
  nlinarith only [hmap,hround,htri,hb]

end NativeRememberedCellHalo

end -- anonymous noncomputable section of native_remembered_cell_halo

/- Source unit: native_remembered_phase_footprint
   Original SHA256: 58801d19dd887dc711ca13e2cbd61d8e7486aa19883cccf5088f4f2d5e21f2ff -/
/- UNVERIFIED fixed-height footprint of an actual old full-phase parent. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeRememberedPhaseFootprint
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalCellChartGeometry NativeCoarseCellSource NativeCoarseDirectionThinning
open NativeFullCoarseShadow NativeDyadicParentCells NativeFullChartTubeGraph
open NativeMatchedShadowConfiguredGeometry

/-- Two actual fine full-source tube incidences in one old phase parent
and one physical height lie within74w. The phase includes intercepts. -/
theorem full_old_phase_diameter {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀i,D.line i∈NativeUnitParentNormalization.fixedCompactClass)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (level b0 c : ℕ) (hb0 : 8 ≤ b0) (hc : c ≤ b0)
    (E : Finset (Fin n × Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀x : E4,O x (3:Fin 4)=x (3:Fin 4))
    (i j : Fin (R.image (parentLabel D a (2^b0))).card)
    (hphase : ancestor b0 c (parentIndex (R.image (parentLabel D a (2^b0))) i)=
      ancestor b0 c (parentIndex (R.image (parentLabel D a (2^b0))) j))
    (x y : E4) (ht : x (3:Fin 4)=y (3:Fin 4))
    (hx : x∈markedUnitTube (MarkedIsometricChart.line O 0 ((fullSource h R a level b0 E).line i))
      (64/((2^b0:ℕ):ℝ)))
    (hy : y∈markedUnitTube (MarkedIsometricChart.line O 0 ((fullSource h R a level b0 E).line j))
      (64/((2^b0:ℕ):ℝ))) :
    dist x y ≤ 74*(64/((2^c:ℕ):ℝ)) := by
  let li := MarkedIsometricChart.line O 0 ((fullSource h R a level b0 E).line i)
  let lj := MarkedIsometricChart.line O 0 ((fullSource h R a level b0 E).line j)
  let ri := representative h R a (2^b0) (parentIndex (R.image (parentLabel D a (2^b0))) i)
  let rj := representative h R a (2^b0) (parentIndex (R.image (parentLabel D a (2^b0))) j)
  have hi := (representative_spec h R a (2^b0) (parentIndex_mem _ i)).2
  have hj := (representative_spec h R a (2^b0) (parentIndex_mem _ j)).2
  have hp : parentLabel D a (2^c) ri=parentLabel D a (2^c) rj := by
    rw [←parent_ancestor_eq D a hc ri,←parent_ancestor_eq D a hc rj,hi,hj]
    exact hphase
  have hg := NativeOriginalPhaseChartGaps.original_phase_chart_gaps h hK ha O hO 0
    (by norm_num) (2^c) (by positivity) ri rj hp
  change (∀v : Fin 3,|slope li v-slope lj v| ≤ 672/((2^c:ℕ):ℝ)) ∧
    ∀v : Fin 3,|intercept li v-intercept lj v| ≤ 672/((2^c:ℕ):ℝ) at hg
  have hxb := full_source_graph_bounds h R a level b0 hb0 E O hO i x hx
  have hyb := full_source_graph_bounds h R a level b0 hb0 E O hO j y hy
  have hscale : 64/((2^b0:ℕ):ℝ) ≤ 64/((2^c:ℕ):ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) hc
  have hsp (v : Fin 3) : |x v.castSucc-y v.castSucc| ≤ 37*(64/((2^c:ℕ):ℝ)) := by
    have he : x v.castSucc-y v.castSucc=
        (x v.castSucc-intercept li v-slope li v*x (3:Fin 4))-
        (y v.castSucc-intercept lj v-slope lj v*y (3:Fin 4))+
        (intercept li v-intercept lj v)+x (3:Fin 4)*(slope li v-slope lj v) := by rw [ht]; ring
    have htprod : |x (3:Fin 4)*(slope li v-slope lj v)| ≤ 672/((2^c:ℕ):ℝ) := by
      rw [abs_mul]
      exact (mul_le_mul hxb.1 (hg.1 v) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
    rw [he]
    have hh := abs_add_le
      ((x v.castSucc-intercept li v-slope li v*x (3:Fin 4))-
        (y v.castSucc-intercept lj v-slope lj v*y (3:Fin 4))+
        (intercept li v-intercept lj v)) (x (3:Fin 4)*(slope li v-slope lj v))
    have hh2 := abs_add_le
      ((x v.castSucc-intercept li v-slope li v*x (3:Fin 4))-
        (y v.castSucc-intercept lj v-slope lj v*y (3:Fin 4))) (intercept li v-intercept lj v)
    have hh3 := abs_sub
      (x v.castSucc-intercept li v-slope li v*x (3:Fin 4))
      (y v.castSucc-intercept lj v-slope lj v*y (3:Fin 4))
    have hxi : |x v.castSucc-intercept li v-slope li v*x (3:Fin 4)| ≤
        8*(64/((2^b0:ℕ):ℝ)) := hxb.2 v
    have hyi : |y v.castSucc-intercept lj v-slope lj v*y (3:Fin 4)| ≤
        8*(64/((2^b0:ℕ):ℝ)) := hyb.2 v
    have hfactor : 672/((2^c:ℕ):ℝ)=(21/2:ℝ)*(64/((2^c:ℕ):ℝ)) := by ring
    have hgi := hg.2 v
    rw [hfactor] at hgi htprod
    linarith only [hh,hh2,hh3,hxi,hyi,hgi,htprod,hscale]
  apply (distance_of_coordinates x y (37*(64/((2^c:ℕ):ℝ))) (by positivity) ?_).trans_eq (by ring)
  intro v
  refine Fin.lastCases ?_ (fun v => hsp v) v
  rw [show (Fin.last 3:Fin 4)=3 by rfl,ht,sub_self,abs_zero]
  positivity

open NativeReferenceXYGridPoints NativeHorizontalGrainSlice CanonicalConfiguredE4Bridge
open NativeLocalParentSource NativeConfiguredIncidenceFibers NativeRelativeParentLabels
open NativeTranslatedGrainHeightOverlap NativeNormalizedCellRelativeMenu
open scoped Matrix.Norms.Elementwise

/-- Same-source version: both points are the original configured map, both
fine tubes are its unchanged full-source representatives, and the old phase
is read through the actual outputTube ancestor identity. -/
theorem actual_configured_diameter {n : ℕ} {D : FiniteScaleSource n} {eta etaS a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (backbone : Finset (Fin n)) (Eref T : Finset (Fin n × Index)) (m : ℕ) (hm : 6 ≤ m)
    (hscale : D.thickness ≤ (rho m)^2) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (NativeLocalParentSource.source h backbone Eref a m p) etaS)
    (hSK : ∀i,(NativeLocalParentSource.source h backbone Eref a m p).line i∈NativeUnitParentNormalization.fixedCompactClass)
    (levelS b0 c : ℕ) (hb0 : 8 ≤ b0) (hc : c ≤ b0)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀t i j,|F t i j| ≤ 1/4) (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ) ≤ 4096/((2^b0:ℕ):ℝ))
    (z z' : Fin n × Index)
    (hz : z∈NativeCubicalIncidenceCounts.incidences original)
    (hz' : z'∈NativeCubicalIncidenceCounts.incidences original)
    (hzP : z.1∈parentLabels D backbone a (2^m) p)
    (hzP' : z'.1∈parentLabels D backbone a (2^m) p)
    (ht : translatedHeight D a m z.2=translatedHeight D a m z'.2)
    (hphase : relativeLabel D a (2^m) p (2^c) z.1=relativeLabel D a (2^m) p (2^c) z'.1) :
    dist (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2)
      (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z'.2) ≤
        74*(64/((2^c:ℕ):ℝ)) := by
  let S := NativeLocalParentSource.source h backbone Eref a m p
  let O := NativePackedFrameIsometry.frame s P hP hd
  let selected := NativeCubicalIncidenceCounts.incidences
    (NativeLocalParentSource.sourceCells D backbone T a (2^m) p)
  let cfg := NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0
  have hTube (v : Fin n × Index) (hv : v∈NativeCubicalIncidenceCounts.incidences original)
      (hvP : v.1∈parentLabels D backbone a (2^m) p) :
      cfg v.2∈markedUnitTube
        (MarkedIsometricChart.line O 0 ((fullSource hS univ 0 levelS b0 selected).line
          (outputTube h backbone Eref a m b0 p hS v.1))) (64/((2^b0:ℕ):ℝ)) := by
    let i := localIndex h backbone Eref a m p hS v.1
    have hr := localIndex_readback h backbone Eref a m p hS v.1 hvP
    have hv' : (NativePaddedCellSource.originalLabel (parentLabels D backbone a (2^m) p) i,v.2)∈
        NativeCubicalIncidenceCounts.incidences original := by rw [hr]; exact hv
    exact NativeActualConfiguredTube.point_mem_full_tube h original horiginal ha backbone Eref m hm
      hscale p hS levelS b0 selected i v.2 hv' s P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
  have hAnc : ancestor b0 c (parentIndex (univ.image (parentLabel S 0 (2^b0)))
      (outputTube h backbone Eref a m b0 p hS z.1))=
      ancestor b0 c (parentIndex (univ.image (parentLabel S 0 (2^b0)))
      (outputTube h backbone Eref a m b0 p hS z'.1)) := by
    rw [outputTube_ancestor_readback h backbone Eref a m b0 c hc p hS z.1 hzP,
      outputTube_ancestor_readback h backbone Eref a m b0 c hc p hS z'.1 hzP']
    exact hphase
  have hTime : cfg z.2 (3:Fin 4)=cfg z'.2 (3:Fin 4) := by
    simp only [cfg,NativeActualConfiguredPoint.point,NativeActualConfiguredPoint.graphGrid_height,
      NativeActualConfiguredPoint.sourceLabel_height,ht]
  exact full_old_phase_diameter hS hSK
    (NativeActualRelativeCoarseAdmission.source_common_height_zero h backbone Eref a m p hS)
    univ levelS b0 c hb0 hc selected O (NativePackedFrameIsometry.frame_height s P hP hd)
    _ _ hAnc _ _ hTime (hTube z hz hzP) (hTube z' hz' hzP')

/-- Convert the configured-point diameter back to literal old physical
cells. This uses the same raw point and the actual first-parent rounding. -/
theorem oldPoint_dist_of_configured {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀t i j,|F t i j| ≤ 1/4) (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    {w : ℝ} (hw : 0 < w) (hmu : mu m ≤ w) (hwidth : mu m*(R0:ℝ) ≤ 64*w)
    (k l : Index)
    (hclose : dist (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 k)
      (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 l) ≤ 74*w) :
    dist (oldPoint D a m p k) (oldPoint D a m p l) ≤ 128*(512*w) := by
  let O := NativePackedFrameIsometry.frame s P hP hd
  let cfg := NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0
  let x := O ((1/512:ℝ) • rawPoint D a m p k)
  let y := O ((1/512:ℝ) • rawPoint D a m p l)
  have hk := NativeActualConfiguredPoint.point_distance D a m hm p s P hP hd F Fcfg hF hCfg R0 hR0 k hbase
  have hl := NativeActualConfiguredPoint.point_distance D a m hm p s P hP hd F Fcfg hF hCfg R0 hR0 l hbase
  have htri := dist_triangle x (cfg k) y
  have htri2 := dist_triangle (cfg k) (cfg l) y
  have hs : dist x y=(1/512:ℝ)*dist (rawPoint D a m p k) (rawPoint D a m p l) := by
    simp only [x,y,O.dist_map,dist_eq_norm,←smul_sub,norm_smul,Real.norm_eq_abs]
    norm_num
  have hraw : dist (rawPoint D a m p k) (rawPoint D a m p l) ≤
      6*(mu m*(R0:ℝ))+512*(74*w) := by
    change dist (cfg k) x ≤ _ at hk
    change dist (cfg l) y ≤ _ at hl
    rw [dist_comm x (cfg k),hs] at htri
    nlinarith only [hk,hl,htri,htri2,hclose]
  have hOldK := physical_rounding h m hm p i hi k
  have hOldL := physical_rounding h m hm p i hi l
  have hOldTri := dist_triangle (oldPoint D a m p k) (rawPoint D a m p k) (oldPoint D a m p l)
  have hOldTri2 := dist_triangle (rawPoint D a m p k) (rawPoint D a m p l) (oldPoint D a m p l)
  rw [dist_comm (oldPoint D a m p k) (rawPoint D a m p k)] at hOldTri
  nlinarith only [hraw,hOldK,hOldL,hOldTri,hOldTri2,hmu,hwidth,hw]


end NativeRememberedPhaseFootprint

end -- anonymous noncomputable section of native_remembered_phase_footprint

/- Source unit: native_remembered_phase_cover
   Original SHA256: 3c568a60c3ddcc9d3d186715f9c0777990ccd9096b15c7191fcf9dd71ce500bd -/
/- UNVERIFIED actual same-T AD-to-cover reader for one old-height/phase
subset. Only the unchanged full reference T supplies AD lower bounds. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeRememberedPhaseCover
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeNormalizedCellRelativeMenu NativeAnisotropicShortRowGeometry NativeTranslatedGrainHeightOverlap
open NativeRememberedPhaseFootprint NativeReferenceXYGridMaps NativeReferenceXYGridField
open NativeSquaredGrainQueries NativeThirdXYData NativeRetainedSliceCore NativeGrainQuotientFibers
open NativeJointLocalXYGeometry NativeLocalParentSource NativeRelativeParentLabels
open NativeFixedCompactKakeyaExponent
open scoped Matrix.Norms.Elementwise

/-- Literal physical labels, with a fixed dimensional menu derived from
the diameter of the actual original physical points. -/
lemma physical_image_card_of_diameter {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m depth : ℕ) (p : Parent) (A : Finset (Fin n × Index))
    (H : ∀z∈A,∀w∈A,dist (oldPoint D a m p z.2) (oldPoint D a m p w.2) ≤
      128*(64/((2^depth:ℕ):ℝ))) :
    (A.image (fun z => physicalCell D a (2^m) (2^depth) p z.2)).card ≤ 257^4 := by
  by_cases hA : A.Nonempty
  · obtain ⟨w,hw⟩ := hA
    have hsub : A.image (fun z => physicalCell D a (2^m) (2^depth) p z.2) ⊆
        columnHalo 128 128 (physicalCell D a (2^m) (2^depth) p w.2) := by
      intro q hq
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
      apply Fintype.mem_piFinset.mpr
      intro j
      simp only [ite_self]
      apply floor_neighbor (by positivity) 128
      have hh : |oldPoint D a m p z.2 j-oldPoint D a m p w.2 j| ≤
          dist (oldPoint D a m p z.2) (oldPoint D a m p w.2) := by
        simpa only [Real.dist_eq] using PiLp.dist_apply_le (oldPoint D a m p z.2) (oldPoint D a m p w.2) j
      exact hh.trans (H z hz w hw)
    exact (card_le_card hsub).trans_eq (by rw [columnHalo_card]; norm_num)
  · simp only [not_nonempty_iff_eq_empty.mp hA,image_empty,card_empty,Nat.zero_le]

/-- A later subset uses the SAME complete T's XY AD. All actual phase and
point geometry is derived here; the output coarse-cover count is not a premise.
The raw query mesh Rd*mu may be512d, independently of the baseline R0. -/
theorem rank_two_from_third {n d J : ℕ} {D : FiniteScaleSource n} {eta etaS a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (backbone : Finset (Fin n)) (Eref : Finset (Fin n × Index))
    (m level : ℕ) (hm : 12 ≤ m) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hf : phaseDepth m ≤ level) (hscale : D.thickness ≤ (rho m)^2) (p : Parent)
    (hRef : IsWangZakharovNativeFiniteInput (NativeLocalParentSource.source h backbone Eref a m p) etaS)
    (hRefK : ∀i,(NativeLocalParentSource.source h backbone Eref a m p).line i∈NativeUnitParentNormalization.fixedCompactClass)
    (levelS b0 c depth : ℕ) (hb0 : 8 ≤ b0) (hc : c ≤ b0) (hdepth : 6 ≤ depth)
    (hwidth : 64/((2^depth:ℕ):ℝ)=512*(64/((2^c:ℕ):ℝ)))
    (plane : Index → Submodule ℝ E4) (E Hgraph S T : Finset (Fin n × Index))
    (hT : T⊆incidences original)
    (hparent : ∀z∈T,z.1∈parentLabels D backbone a (2^m) p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (Fraw Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (population PL PU : ℝ) (Qref : ℕ) (lambda G Cpre threshold : ℝ) (L3 : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (Hdata : HasThirdXYData (J:=J) (ell:=2) D zeta a m plane E Hgraph S T P hP
      (by norm_num) (by norm_num) hd Fraw p population PL PU Qref lambda G Cpre threshold L3 Rel)
    (R0 Rd : ℕ) (hR0 : 0 < R0) (hRd : 0 < Rd)
    (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ) ≤ 4096/((2^b0:ℕ):ℝ))
    (hsmall : 512*mu m ≤ 64/((2^depth:ℕ):ℝ))
    (hquery : (Rd:ℝ)*mu m ≤ 64/((2^depth:ℕ):ℝ))
    (hkappa : extremalExponent ≤ 3)
    (A : Finset (Fin n × Index)) (hAT : A⊆T) (height : ℤ) (q : Parent)
    (hHeight : ∀z∈A,translatedHeight D a m z.2=height)
    (hPhase : ∀z∈A,relativeLabel D a (2^m) p (2^c) z.1=q) :
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P hP
      (by norm_num) (by norm_num) hd (physicalMesh m (phaseDepth m)/8)
    let F := fixedField D a m 2 plane Sq Fraw
    let Q3 := NativeSourceSizeBounds.radix S.card L3
    let F3 := refinementCost (d+2) (J+1) L3
    let K := xyConstant D.thickness zeta population PL PU lambda (G*Cpre*(F3:ℝ)) Qref Q3 J m
    ((A.image (fun z => coarseXY 2 Rd (pxy D a m 2 p P hP (by norm_num) (by norm_num) hd F z.2))).card:ℝ) ≤
      (257^4:ℝ)*(9^3:ℝ)*(13^3:ℝ)^2*K^2*6^(3-extremalExponent)*
        ((6*(64/((2^depth:ℕ):ℝ)))/((Rd:ℝ)*mu m))^(3-extremalExponent) := by
  intro Sq F Q3 F3 K
  have Hcopy := Hdata
  rcases Hcopy with ⟨_hTS,_hTn,_hCost,_hTH,_hFinal,_hExtra,_hOld,_hXY,_hClass,
    _hGrain,_hKey,_hThreshold,_hRet,Hxy,_hRead,hNorm⟩
  have hF : ∀t i j,|F t i j| ≤ 1/4 := by
    intro t i j
    simpa only [Real.norm_eq_abs] using (Matrix.norm_le_iff (by norm_num : (0:ℝ) ≤ 1/4)).mp (hNorm t) i j
  let physical := fun z : Fin n × Index => physicalCell D a (2^m) (2^depth) p z.2
  let xy := fun z : Fin n × Index => coarseXY 2 Rd (pxy D a m 2 p P hP (by norm_num) (by norm_num) hd F z.2)
  let C : ℝ := (9^3:ℝ)*(13^3:ℝ)^2*K^2*6^(3-extremalExponent)*
    ((6*(64/((2^depth:ℕ):ℝ)))/((Rd:ℝ)*mu m))^(3-extremalExponent)
  have hC : 0 ≤ C := by have hmuPos := mu_pos m; dsimp only [C]; positivity
  have hK : 1 ≤ K := xyConstant_one_le _ _ _ _ _ _ _ _ _ _ _
  have hCard : (A.image physical).card ≤ 257^4 := by
    apply physical_image_card_of_diameter D a m depth p A
    intro z hz w hw
    have hcfg := actual_configured_diameter h original horiginal ha backbone Eref T m (by omega)
      hscale p hRef hRefK levelS b0 c hb0 hc .oneTwo P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
      z w (hT (hAT hz)) (hT (hAT hw)) (hparent z (hAT hz)) (hparent w (hAT hw))
      ((hHeight z hz).trans (hHeight w hw).symm) ((hPhase z hz).trans (hPhase w hw).symm)
    have hcw : 64/((2^b0:ℕ):ℝ) ≤ 64/((2^c:ℕ):ℝ) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) hc
    have hbasew : mu m*(R0:ℝ) ≤ 64*(64/((2^c:ℕ):ℝ)) := by
      have hh := mul_le_mul_of_nonneg_left hcw (by norm_num : (0:ℝ) ≤ 64)
      have he : 4096/((2^b0:ℕ):ℝ)=64*(64/((2^b0:ℕ):ℝ)) := by ring
      rw [he] at hmatch
      exact hmatch.trans hh
    have hmuw : mu m ≤ 64/((2^c:ℕ):ℝ) := by rw [hwidth] at hsmall; linarith only [hsmall]
    have ho := oldPoint_dist_of_configured h m (by omega) p z.1
      ((mem_parentLabels D backbone a (2^m) p _).mp (hparent z (hAT hz))).2
      .oneTwo P hP hd F Fcfg hF hCfg R0 hR0 hbase (by positivity) hmuw hbasew z.2 w.2 hcfg
    simpa only [hwidth] using ho
  have hLocal (v : Index) (_hv : v∈A.image physical) :
      (((A.filter (fun z => physical z=v)).image xy).card:ℝ) ≤ C := by
    let U := A.filter (fun z => physical z=v)
    by_cases hU : U.Nonempty
    · obtain ⟨anchor,hanchor⟩ := hU
      have hUT : U⊆T := (filter_subset _ _).trans hAT
      have hh := source_height_cell_base_keys h original horiginal ha m level 2 hm hdy hf p U T hUT
        hT (fun z hz => ((mem_parentLabels D backbone a (2^m) p _).mp (hparent z hz)).2)
        P hP (by norm_num) (by norm_num) hd F hNorm Rd depth hRd hdepth hsmall hquery
        anchor hanchor
        (fun z hz => (hHeight z (mem_filter.mp hz).1).trans (hHeight anchor (mem_filter.mp hanchor).1).symm)
        (fun z hz => (mem_filter.mp hz).2.trans (mem_filter.mp hanchor).2.symm)
        hK (by linarith only [hkappa]) (Hxy (translatedHeight D a m anchor.2))
      simpa only [U,xy,C,Nat.cast_pow,Nat.cast_ofNat] using hh
    · simp only [U,not_nonempty_iff_eq_empty.mp hU,image_empty,card_empty,Nat.cast_zero]
      exact hC
  have hh := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images A xy physical C hLocal
  have hreal : ((A.image physical).card:ℝ) ≤ (257^4:ℝ) := by exact_mod_cast hCard
  have hbound := mul_le_mul_of_nonneg_left hreal hC
  exact hh.trans (by dsimp only [C] at hbound ⊢; simpa only [mul_assoc,mul_left_comm,mul_comm] using hbound)

end NativeRememberedPhaseCover

end -- anonymous noncomputable section of native_remembered_phase_cover

/- Source unit: native_remembered_cell_fibers
   Original SHA256: 5449ca78b5f960e6e7808c7dffefbb507d8baab27a970342714a465bdd81a125 -/
/- UNVERIFIED fixed capacity of the ACTUAL final local-cell image over one
original coarse XY key. Original occurrences remain the witnesses. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeRememberedCellFibers
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeReferenceXYGridPoints NativeReferenceXYGridMaps NativeReferenceXYGridLinear
open NativeReferenceXYGridMetric NativeHorizontalGrainSlice NativeLocalParentSource
open NativeRememberedCellHalo NativeRememberedSourceMaps NativeJointSpatialGeometry
open NativeLocalCellCoherence NativeOriginalCellChartGeometry NativeAnisotropicShortRowGeometry
open CanonicalConfiguredE4Bridge NativeMatchedShadowConfiguredGeometry
open scoped Matrix.Norms.Elementwise

/-- Equal coarse XY keys include an exact common old height. At raw mesh
512d, the actual configured points are within16d, with all rounding paid. -/
theorem configured_gap_of_coarse_XY {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hF : ∀t,‖F t‖ ≤ (1/4:ℝ)) (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (R0 Rd : ℕ) (hR0 : 0 < R0) (hRd : 512 ≤ Rd)
    (hbase : rho m ≤ mu m*(R0:ℝ))
    {d : ℝ} (hdpos : 0 < d) (hmu : mu m ≤ d) (hbaseD : mu m*(R0:ℝ) ≤ 64*d)
    (hmesh : (Rd:ℝ)*mu m=512*d) (k l : Index)
    (hxy : coarseXY 2 Rd (pxy D a m 2 p P hP (by norm_num) (by norm_num) hd F k)=
      coarseXY 2 Rd (pxy D a m 2 p P hP (by norm_num) (by norm_num) hd F l)) :
    dist (NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 k)
      (NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 l) ≤ 16*d := by
  have hOld := coarse_xy_old_dist h m 2 hm p i hi P hP (by norm_num) (by norm_num) hd F hF Rd hRd k l hxy
  rw [hmesh] at hOld
  have hraw0 := raw_dist_le_old h m hm p i hi k l
  have hraw : dist (rawPoint D a m p k) (rawPoint D a m p l) ≤ 8*(512*d)+256*mu m := by
    linarith only [hraw0,hOld]
  have hFe : ∀t i j,|F t i j| ≤ 1/4 := by
    intro t i j
    simpa only [Real.norm_eq_abs] using (Matrix.norm_le_iff (by norm_num : (0:ℝ) ≤ 1/4)).mp (hF t) i j
  let O := NativePackedFrameIsometry.frame .oneTwo P hP hd
  let cfg := NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0
  let x := O ((1/512:ℝ) • rawPoint D a m p k)
  let y := O ((1/512:ℝ) • rawPoint D a m p l)
  have hk := NativeActualConfiguredPoint.point_distance D a m hm p .oneTwo P hP hd F Fcfg hFe hCfg R0 hR0 k hbase
  have hl := NativeActualConfiguredPoint.point_distance D a m hm p .oneTwo P hP hd F Fcfg hFe hCfg R0 hR0 l hbase
  have hs : dist x y=(1/512:ℝ)*dist (rawPoint D a m p k) (rawPoint D a m p l) := by
    simp only [x,y,O.dist_map,dist_eq_norm,←smul_sub,norm_smul,Real.norm_eq_abs]
    norm_num
  have h1 := dist_triangle (cfg k) x (cfg l)
  have h2 := dist_triangle x y (cfg l)
  change dist (cfg k) x ≤ _ at hk
  change dist (cfg l) y ≤ _ at hl
  rw [dist_comm y (cfg l),hs] at h2
  nlinarith only [h1,h2,hk,hl,hraw,hmu,hbaseD,hdpos]

/-- The literal integer cell centers have a fixed finite halo whenever
their actual Euclidean diameter is at most24sigma. No direction count occurs. -/
lemma local_cell_image_cap {X : Type*} (A : Finset X) (cell : X → Index)
    {sigma : ℝ} (hs : 0 < sigma)
    (H : ∀x∈A,∀y∈A,
      dist (cellCenter (sigma/2) (cell x)) (cellCenter (sigma/2) (cell y)) ≤ 24*sigma) :
    (A.image cell).card ≤ 129^4 := by
  by_cases hA : A.Nonempty
  · obtain ⟨y,hy⟩ := hA
    have hsub : A.image cell⊆columnHalo 64 64 (cell y) := by
      intro k hk
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hk
      apply Fintype.mem_piFinset.mpr
      intro j
      simp only [ite_self]
      have hh : |cellCenter (sigma/2) (cell x) j-cellCenter (sigma/2) (cell y) j| ≤ 24*sigma := by
        exact (show _ ≤ dist (cellCenter (sigma/2) (cell x)) (cellCenter (sigma/2) (cell y)) by
          simpa only [Real.dist_eq] using PiLp.dist_apply_le
            (cellCenter (sigma/2) (cell x)) (cellCenter (sigma/2) (cell y)) j).trans (H x hx y hy)
      have he : cellCenter (sigma/2) (cell x) j-cellCenter (sigma/2) (cell y) j =
          (sigma/2)*(((cell x j:ℤ):ℝ)-((cell y j:ℤ):ℝ)) := by dsimp [cellCenter]; ring
      rw [he,abs_mul,abs_of_pos (half_pos hs)] at hh
      have hi : |((cell x j:ℤ):ℝ)-((cell y j:ℤ):ℝ)| ≤ 64 := by
        nlinarith only [hh,hs]
      have hz : |cell x j-cell y j| ≤ (64:ℤ) := by exact_mod_cast hi
      have hzBounds := abs_le.mp hz
      exact mem_Icc.mpr ⟨by omega,by omega⟩
    exact (card_le_card hsub).trans_eq (by rw [columnHalo_card]; norm_num)
  · simp only [not_nonempty_iff_eq_empty.mp hA,image_empty,card_empty,Nat.zero_le]

/-- Combine the actual4sigma occurrence halo with a16d original-point
cluster. The common parent physical map contributes precisely N/64. -/
theorem local_centers_cluster {n : ℕ} {C : FiniteScaleSource n} {eta : ℝ}
    (hC : IsWangZakharovNativeFiniteInput C eta) (N : ℕ) (hN : 0 < N) (p : Parent)
    (i : Fin n) (hi : parentLabel C 0 N i=p)
    (O : E4 ≃ₗᵢ[ℝ] E4) (x y : E4) (j k : Index)
    (hx : dist (cellCenter ((N:ℝ)*C.thickness/128) j)
      (NativeLocalParentPhysicalMap.physicalMap C 0 N p (O.symm x)) ≤ 4*((N:ℝ)*C.thickness/64))
    (hy : dist (cellCenter ((N:ℝ)*C.thickness/128) k)
      (NativeLocalParentPhysicalMap.physicalMap C 0 N p (O.symm y)) ≤ 4*((N:ℝ)*C.thickness/64))
    (hxy : dist x y ≤ 16*C.thickness) :
    dist (cellCenter ((N:ℝ)*C.thickness/128) j)
      (cellCenter ((N:ℝ)*C.thickness/128) k) ≤ 24*((N:ℝ)*C.thickness/64) := by
  have hm := physical_map_dist hC 0 N hN p i hi (O.symm x) (O.symm y)
  rw [O.symm.dist_map] at hm
  have hm' := mul_le_mul_of_nonneg_left hxy (show (0:ℝ) ≤ N by positivity)
  have h1 := dist_triangle (cellCenter ((N:ℝ)*C.thickness/128) j)
    (NativeLocalParentPhysicalMap.physicalMap C 0 N p (O.symm x))
    (cellCenter ((N:ℝ)*C.thickness/128) k)
  have h2 := dist_triangle (NativeLocalParentPhysicalMap.physicalMap C 0 N p (O.symm x))
    (NativeLocalParentPhysicalMap.physicalMap C 0 N p (O.symm y))
    (cellCenter ((N:ℝ)*C.thickness/128) k)
  have hy' : dist (NativeLocalParentPhysicalMap.physicalMap C 0 N p (O.symm y))
      (cellCenter ((N:ℝ)*C.thickness/128) k) ≤ 4*((N:ℝ)*C.thickness/64) := by
    simpa only [dist_comm] using hy
  nlinarith only [hx,hy',hxy,hm,hm',h1,h2]

/-- Every fiber over an actual original coarse XY key has at most129^4
final cell labels. Both halo inputs are derived from its original occurrences. -/
theorem actual_fiber_card {n : ℕ} {D : FiniteScaleSource n} {eta etaC a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (backbone : Finset (Fin n)) (m b : ℕ) (hm : 6 ≤ m) (p : Parent)
    (hp : (parentLabels D backbone a (2^m) p).Nonempty)
    (hNscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (hRelScale : ((2^m:ℕ):ℝ)*D.thickness*((2^b:ℕ):ℝ) ≤ 64)
    (Q : Finset Parent) (C : FiniteScaleSource Q.card)
    (hC : IsWangZakharovNativeFiniteInput C etaC)
    (cells : Fin Q.card → Finset Index) (hcells : ∀i,C.shading i=wzCellShading (mesh C) cells i)
    (haC : ∀i,wzGraphTime (C.line i) 0-mark (C.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (hthickness : C.thickness=64/((2^b:ℕ):ℝ))
    (A : Finset (Fin n × Index)) (hA : A⊆NativeCubicalIncidenceCounts.incidences original)
    (hparent : ∀z∈A,z.1∈parentLabels D backbone a (2^m) p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hF : ∀t,‖F t‖ ≤ (1/4:ℝ)) (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (R0 Rd : ℕ) (hR0 : 0 < R0) (hRd : 512 ≤ Rd)
    (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ) ≤ 4096/((2^b:ℕ):ℝ))
    (hmesh : (Rd:ℝ)*mu m=512*C.thickness)
    (c : ℕ) (pA : Parent)
    (V : Finset ((Fin Q.card × Index) × (Fin n × Index)))
    (hV : V⊆occurrences h backbone a m b p hp Q cells A)
    (hcurrent : ∀z∈V,parentLabel C 0 (2^c) z.1.1=pA)
    (q : NativeReferenceXYGridMaps.XY 2) :
    (((V.filter (fun z => coarseXY 2 Rd
      (pxy D a m 2 p P hP (by norm_num) (by norm_num) hd F z.2.2)=q)).image
      (fun z => localCellLabel C 0 (2^c) pA z.1)).card) ≤ 129^4 := by
  let U := V.filter (fun z => coarseXY 2 Rd
    (pxy D a m 2 p P hP (by norm_num) (by norm_num) hd F z.2.2)=q)
  have hFe : ∀t i j,|F t i j| ≤ 1/4 := by
    intro t i j
    simpa only [Real.norm_eq_abs] using (Matrix.norm_le_iff (by norm_num : (0:ℝ) ≤ 1/4)).mp (hF t) i j
  have hBaseD : mu m*(R0:ℝ) ≤ 64*C.thickness := by rw [hthickness]; convert hmatch using 1; ring
  have hmu : mu m ≤ C.thickness := by
    have hr : rho m=64*mu m := by unfold NativeReferenceXYGridPoints.mu; ring
    rw [hr] at hbase
    linarith only [hbase,hBaseD]
  let O := NativePackedFrameIsometry.frame .oneTwo P hP hd
  let cfg := NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0
  have halo (z : (Fin Q.card × Index) × (Fin n × Index)) (hz : z∈U) :
      dist (cellCenter (((2^c:ℕ):ℝ)*C.thickness/128) (localCellLabel C 0 (2^c) pA z.1))
        (NativeLocalParentPhysicalMap.physicalMap C 0 (2^c) pA (O.symm (cfg z.2.2))) ≤
          4*(((2^c:ℕ):ℝ)*C.thickness/64) :=
    occurrence_center_near h original horiginal ha backbone m b hm p hp hNscale hRelScale Q C hC
      cells hcells haC hthickness A hA hparent .oneTwo P hP hd F Fcfg hFe hCfg R0 hR0 hbase hmatch
      c pA z (hV (mem_filter.mp hz).1) (hcurrent z (mem_filter.mp hz).1)
  have hs : 0 < ((2^c:ℕ):ℝ)*C.thickness/64 := by have hc := hC.1.2.1; positivity
  apply local_cell_image_cap U (fun z => localCellLabel C 0 (2^c) pA z.1) hs
  intro z hz w hw
  have hzA := ((mem_occurrences h backbone a m b p hp Q cells A z).mp (hV (mem_filter.mp hz).1)).2.1
  have hOldParent := (mem_parentLabels D backbone a (2^m) p _).mp (hparent z.2 hzA)
  have hGap := configured_gap_of_coarse_XY h m hm p z.2.1 hOldParent.2 P hP hd F Fcfg hF hCfg
    R0 Rd hR0 hRd hbase hC.1.2.1 hmu hBaseD hmesh z.2.2 w.2.2
    ((mem_filter.mp hz).2.trans (mem_filter.mp hw).2.symm)
  have hh := local_centers_cluster hC (2^c) (by positivity) pA z.1.1
    (hcurrent z (mem_filter.mp hz).1) O (cfg z.2.2) (cfg w.2.2)
    (localCellLabel C 0 (2^c) pA z.1) (localCellLabel C 0 (2^c) pA w.1) (halo z hz) (halo w hw) hGap
  have he : (((2^c:ℕ):ℝ)*C.thickness/64)/2=((2^c:ℕ):ℝ)*C.thickness/128 := by ring
  simpa only [he] using hh


end NativeRememberedCellFibers

end -- anonymous noncomputable section of native_remembered_cell_fibers

/- Source unit: native_remembered_time_upper
   Original SHA256: f619c93dd0fc555a5affd674775a313fe141e92224a311151167f4fd52354aa4 -/
/- UNVERIFIED unconditional time support upper for the literal local source. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeRememberedTimeUpper
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalCellChartGeometry NativeLocalParentCells NativeLocalCellCoherence
open NativeConfiguredTimeCoarsening NativeConfiguredHeightCaps

/-- All retained native local cells have center height in[-1,1]. This uses
the actual intermediate shading, not an assumed output support box. -/
theorem local_center_time_bound {n : ℕ} {C : FiniteScaleSource n} {eta : ℝ}
    (hC : IsWangZakharovNativeFiniteInput C eta) (cells : Fin n → Finset Index)
    (hcells : ∀i,C.shading i=wzCellShading (mesh C) cells i)
    (ha : ∀i,wzGraphTime (C.line i) 0-mark (C.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (hs1 : (N:ℝ)*C.thickness/64 ≤ 1)
    (i : Fin n) (k : Index) (hk : k∈cells i) :
    |cellCenter ((N:ℝ)*C.thickness/128) (localCellLabel C 0 N p (i,k)) (3:Fin 4)| ≤ 1 := by
  have hd := hC.1.2.1
  have he : 0 < (N:ℝ)*C.thickness/128 := by positivity
  have ho := (NativeOriginalParentPhysicalData.original_cell_bounds hC cells hcells 0 ha
    ((NativeCubicalIncidenceCounts.mem_incidences cells i k).mpr hk)).1
  change |NativeOriginalPaddedCells.oldTime C 0 k| ≤ 1 at ho
  have hf : |frontPoint C 0 N p i k (3:Fin 4)| ≤ 1/128 := by
    rw [frontPoint_height,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 128)]
    exact div_le_div_of_nonneg_right ho (by norm_num)
  have hr := NativeRelativeCoarseGeometry.cell_center_coordinate_error he (frontPoint C 0 N p i k) (3:Fin 4)
  change |cellCenter ((N:ℝ)*C.thickness/128) (localCellLabel C 0 N p (i,k)) (3:Fin 4)-
    frontPoint C 0 N p i k (3:Fin 4)| ≤ _ at hr
  have ht := abs_sub_le
    (cellCenter ((N:ℝ)*C.thickness/128) (localCellLabel C 0 N p (i,k)) (3:Fin 4))
    (frontPoint C 0 N p i k (3:Fin 4)) 0
  rw [sub_zero,sub_zero] at ht
  linarith only [hf,hr,ht,hs1]

/-- The actual integer final time image has at most6/sigma labels. No
height lower bound or equal occupancy of different bins is used. -/
theorem local_time_card {n : ℕ} {C : FiniteScaleSource n} {eta : ℝ}
    (hC : IsWangZakharovNativeFiniteInput C eta) (cells : Fin n → Finset Index)
    (hcells : ∀i,C.shading i=wzCellShading (mesh C) cells i)
    (ha : ∀i,wzGraphTime (C.line i) 0-mark (C.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (hs1 : (N:ℝ)*C.thickness/64 ≤ 1)
    (E : Finset (Fin n × Index)) (hE : E⊆NativeCubicalIncidenceCounts.incidences cells) :
    ((E.image (fun z => localCellLabel C 0 N p z (3:Fin 4))).card:ℝ) ≤
      6/((N:ℝ)*C.thickness/64) := by
  let sigma : ℝ := (N:ℝ)*C.thickness/64
  have hs : 0 < sigma := by dsimp [sigma]; have hd := hC.1.2.1; positivity
  let H := E.image (fun z => localCellLabel C 0 N p z (3:Fin 4))
  let time := finalTime (256*sigma)
  have htime (z : Fin n × Index) : time (localCellLabel C 0 N p z (3:Fin 4))=
      cellCenter ((N:ℝ)*C.thickness/128) (localCellLabel C 0 N p z) (3:Fin 4) := by
    dsimp [time,finalTime,sigma,cellCenter]
    ring
  have hbox : ∀t∈H.image time,(-1:ℝ) ≤ t ∧ t ≤ -1+2 := by
    intro t ht
    obtain ⟨j,hj,rfl⟩ := mem_image.mp ht
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hj
    rw [htime]
    have hb := local_center_time_bound hC cells hcells ha N hN p hs1 z.1 z.2
      ((NativeCubicalIncidenceCounts.mem_incidences cells _ _).mp (hE hz))
    simpa only [show (-1:ℝ)+2=1 by norm_num] using abs_le.mp hb
  have hcard : (H.image time).card=H.card := by
    apply card_image_of_injective
    intro x y he
    have hm : 256*sigma/512 ≠ 0 := by positivity
    change (256*sigma/512)*((x:ℝ)+1/2)=(256*sigma/512)*((y:ℝ)+1/2) at he
    exact_mod_cast add_right_cancel (mul_left_cancel₀ hm he)
  have hh := unconditional_interval_cap H (256*sigma) (by positivity) (-1) 2 (by norm_num)
  change (((H.image time).filter (fun z => -1≤z ∧ z≤-1+2)).card:ℝ) ≤ _ at hh
  rw [filter_eq_self.mpr hbox,hcard] at hh
  have hm := mul_le_mul_of_nonneg_right hh hs.le
  have he : (2/(256*sigma/512)+2)*sigma=4+2*sigma := by field_simp [hs.ne']; ring
  rw [he] at hm
  apply (le_div_iff₀ hs).mpr
  change sigma ≤ 1 at hs1
  linarith only [hm,hs1]

end NativeRememberedTimeUpper

end -- anonymous noncomputable section of native_remembered_time_upper

/- Source unit: native_remembered_source_union
   Original SHA256: 848685e47b02e49e888aaaa92413acb0ef73a9ea1e791d36a86e9ae662714488 -/
/- UNVERIFIED actual remembered-source union upper. The only AD input is
HasThirdXYData on the unchanged complete T. Later restrictions use original
occurrences and one actual old height per final native cell-time label. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeRememberedSourceUnion
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeLocalParentSource NativeRelativeParentLabels
open NativeReferenceXYGridPoints NativeReferenceXYGridMaps NativeReferenceXYGridField
open NativeHorizontalGrainSlice NativeSquaredGrainQueries NativeThirdXYData NativeRetainedSliceCore
open NativeGrainQuotientFibers NativeTranslatedGrainHeightOverlap NativeFixedCompactKakeyaExponent
open NativeRememberedSourceMaps NativeRememberedPhaseCover NativeRememberedCellFibers NativeRememberedTimeUpper
open NativeLocalCellCoherence
open scoped ENNReal Matrix.Norms.Elementwise

/-- All source-dependent loss is the actual complete-slice constant K squared. -/
def unionConstant (K : ℝ) : ℝ :=
  (129^4:ℝ)*(257^4:ℝ)*(9^3:ℝ)*(13^3:ℝ)^2*K^2*(36:ℝ)^(3-extremalExponent)

/-- Literal same-T source join: original old-phase geometry, complete-slice
AD, actual intermediate shadows, final local cells, and the chosen old-height
relation are composed. Neither an output point-count upper nor a subset AD
lower is assumed. -/
theorem rank_two_union {n d J : ℕ} {D : FiniteScaleSource n} {eta etaS etaC a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (backbone : Finset (Fin n)) (Eref : Finset (Fin n × Index))
    (m level : ℕ) (hm : 12 ≤ m) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hf : phaseDepth m ≤ level) (hscale : D.thickness ≤ (rho m)^2) (p : Parent)
    (hRef : IsWangZakharovNativeFiniteInput (NativeLocalParentSource.source h backbone Eref a m p) etaS)
    (hRefK : ∀i,(NativeLocalParentSource.source h backbone Eref a m p).line i∈NativeUnitParentNormalization.fixedCompactClass)
    (levelS b0 c depth : ℕ) (hb0 : 8 ≤ b0) (hc : c ≤ b0) (hdepth : 6 ≤ depth)
    (hwidth : 64/((2^depth:ℕ):ℝ)=512*(64/((2^c:ℕ):ℝ)))
    (plane : Index → Submodule ℝ E4) (E Hgraph S T : Finset (Fin n × Index))
    (hT : T⊆incidences original)
    (hparent : ∀z∈T,z.1∈parentLabels D backbone a (2^m) p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (Fraw Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (population PL PU : ℝ) (Qref : ℕ) (lambda G Cpre threshold : ℝ) (L3 : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (Hdata : HasThirdXYData (J:=J) (ell:=2) D zeta a m plane E Hgraph S T P hP
      (by norm_num) (by norm_num) hd Fraw p population PL PU Qref lambda G Cpre threshold L3 Rel)
    (R0 Rd : ℕ) (hR0 : 0 < R0) (hRd : 0 < Rd)
    (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ) ≤ 4096/((2^b0:ℕ):ℝ))
    (hsmall : 512*mu m ≤ 64/((2^depth:ℕ):ℝ))
    (hquery : (Rd:ℝ)*mu m ≤ 64/((2^depth:ℕ):ℝ))
    (hkappa : extremalExponent ≤ 3)
    (A : Finset (Fin n × Index)) (hAT : A⊆T) (qOld : Parent)
    (hPhase : ∀z∈A,relativeLabel D a (2^m) p (2^c) z.1=qOld)
    (b : ℕ) (hbb : b ≤ b0)
    (hNscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (hRelScale : ((2^m:ℕ):ℝ)*D.thickness*((2^b:ℕ):ℝ) ≤ 64)
    (Qmid : Finset Parent) (C : FiniteScaleSource Qmid.card)
    (hC : IsWangZakharovNativeFiniteInput C etaC)
    (cells : Fin Qmid.card → Finset Index) (hcells : ∀i,C.shading i=wzCellShading (mesh C) cells i)
    (haC : ∀i,wzGraphTime (C.line i) 0-mark (C.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (hCthick : C.thickness=64/((2^b:ℕ):ℝ))
    (hRd512 : 512 ≤ Rd) (hRdMesh : (Rd:ℝ)*mu m=512*C.thickness)
    (pA : Parent) (hsigma : ((2^c:ℕ):ℝ)*C.thickness/64 ≤ 1) :
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P hP
      (by norm_num) (by norm_num) hd (physicalMesh m (phaseDepth m)/8)
    let _F := fixedField D a m 2 plane Sq Fraw
    let Q3 := NativeSourceSizeBounds.radix S.card L3
    let F3 := refinementCost (d+2) (J+1) L3
    let K := xyConstant D.thickness zeta population PL PU lambda (G*Cpre*(F3:ℝ)) Qref Q3 J m
    let hp : (parentLabels D backbone a (2^m) p).Nonempty := card_pos.mp hRef.1.1
    let O := occurrences h backbone a m b p hp Qmid cells A
    ∀B⊆O.image (taggedKey D a m C c pA),
      (∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1) →
      let Efinal := selectedPairs D a m C c pA O B
      (∀z∈Efinal,z.1∈parentLabels C univ 0 (2^c) pA) →
      volume (sourceUnion (NativeLocalParentSource.source hC univ Efinal 0 c pA)) ≤
        ENNReal.ofReal (unionConstant K*(((2^c:ℕ):ℝ)*C.thickness/64)^extremalExponent) := by
  intro Sq F Q3 F3 K hp O B hBO hHeightChoice Efinal hParentFinal
  let V := selectedOccurrences D a m C c pA O B
  let cell := fun z : (Fin Qmid.card × Index) × (Fin n × Index) => localCellLabel C 0 (2^c) pA z.1
  let time := fun z : (Fin Qmid.card × Index) × (Fin n × Index) => cell z (3:Fin 4)
  let xy := fun z : Fin n × Index => coarseXY 2 Rd (pxy D a m 2 p P hP (by norm_num) (by norm_num) hd F z.2)
  let sigma : ℝ := ((2^c:ℕ):ℝ)*C.thickness/64
  let Cover : ℝ := (257^4:ℝ)*(9^3:ℝ)*(13^3:ℝ)^2*K^2*6^(3-extremalExponent)*
    ((6*(64/((2^depth:ℕ):ℝ)))/((Rd:ℝ)*mu m))^(3-extremalExponent)
  have hs : 0 < sigma := by dsimp [sigma]; have hdC := hC.1.2.1; positivity
  have hCover : 0 ≤ Cover := by have hmuPos := mu_pos m; dsimp only [Cover]; positivity
  have Hcopy := Hdata
  rcases Hcopy with ⟨_hTS,_hTn,_hCost,_hTH,_hFinal,_hExtra,_hOld,_hXY,_hClass,
    _hGrain,_hKey,_hThreshold,_hRet,_Hxy,_hRead,hNorm⟩
  have hVO : V⊆O := filter_subset _ _
  have hOrig (z : (Fin Qmid.card × Index) × (Fin n × Index)) (hz : z∈V) : z.2∈A :=
    ((mem_occurrences h backbone a m b p hp Qmid cells A z).mp (hVO hz)).2.1
  have hEinc : Efinal⊆incidences cells := by
    intro z hz
    obtain ⟨v,hv,he⟩ := mem_image.mp hz
    rw [←he]
    exact ((mem_occurrences h backbone a m b p hp Qmid cells A v).mp (hVO hv)).1
  have hCurrent (z : (Fin Qmid.card × Index) × (Fin n × Index)) (hz : z∈V) :
      parentLabel C 0 (2^c) z.1.1=pA :=
    ((mem_parentLabels C univ 0 (2^c) pA _).mp (hParentFinal z.1 (mem_image_of_mem _ hz))).2
  have hmatchb : mu m*(R0:ℝ) ≤ 4096/((2^b:ℕ):ℝ) := by
    apply hmatch.trans
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) hbb
  have hLocal (j : ℤ) (hj : j∈V.image time) :
      (((V.filter (fun z => time z=j)).image cell).card:ℝ) ≤ (129^4:ℝ)*Cover := by
    let W := V.filter (fun z => time z=j)
    obtain ⟨anchor,hanchorV,hanchorTime⟩ := mem_image.mp hj
    have hanchor : anchor∈W := mem_filter.mpr ⟨hanchorV,hanchorTime⟩
    let U := W.image Prod.snd
    have hUA : U⊆A := by
      intro z hz
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
      exact hOrig w (mem_filter.mp hw).1
    have hUT : U⊆T := hUA.trans hAT
    have hOldHeight : ∀z∈U,translatedHeight D a m z.2=translatedHeight D a m anchor.2.2 := by
      intro z hz
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
      exact hHeightChoice (taggedKey D a m C c pA w) (mem_filter.mp (mem_filter.mp hw).1).2
        (taggedKey D a m C c pA anchor) (mem_filter.mp hanchorV).2
        ((mem_filter.mp hw).2.trans hanchorTime.symm)
    have hXY := rank_two_from_third h original horiginal ha backbone Eref m level hm hdy hf hscale p
      hRef hRefK levelS b0 c depth hb0 hc hdepth hwidth plane E Hgraph S T hT hparent
      P hP hd Fraw Fcfg hCfg population PL PU Qref lambda G Cpre threshold L3 Rel Hdata
      R0 Rd hR0 hRd hbase hmatch hsmall hquery hkappa U hUT
      (translatedHeight D a m anchor.2.2) qOld hOldHeight (fun z hz => hPhase z (hUA hz))
    have hXY' : ((W.image (fun z => xy z.2)).card:ℝ) ≤ Cover := by
      change ((U.image xy).card:ℝ) ≤ Cover at hXY
      simpa only [U,image_image,Function.comp_def] using hXY
    have hFiber (q : NativeReferenceXYGridMaps.XY 2) (_hq : q∈W.image (fun z => xy z.2)) :
        (((W.filter (fun z => xy z.2=q)).image cell).card:ℝ) ≤ (129^4:ℝ) := by
      exact_mod_cast actual_fiber_card h original horiginal ha backbone m b (by omega) p hp hNscale hRelScale
        Qmid C hC cells hcells haC hCthick A (hAT.trans hT) (fun z hz => hparent z (hAT hz))
        P hP hd F Fcfg hNorm hCfg R0 Rd hR0 hRd512 hbase hmatchb hRdMesh c pA W
        ((filter_subset _ _).trans hVO) (fun z hz => hCurrent z (mem_filter.mp hz).1) q
    have hh := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images W cell
      (fun z => xy z.2) (129^4:ℝ) hFiber
    exact hh.trans (mul_le_mul_of_nonneg_left hXY' (by positivity))
  have hSupport := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images V cell time
    ((129^4:ℝ)*Cover) hLocal
  have hTime := local_time_card hC cells hcells haC (2^c) (by positivity) pA hsigma Efinal hEinc
  have hTimeRead : Efinal.image (fun z => localCellLabel C 0 (2^c) pA z (3:Fin 4))=V.image time := by
    rw [show Efinal=V.image Prod.fst from rfl,image_image]
    rfl
  rw [hTimeRead] at hTime
  have hSupportRead : Efinal.image (localCellLabel C 0 (2^c) pA)=V.image cell := by
    rw [show Efinal=V.image Prod.fst from rfl,image_image]
    rfl
  have hCount : ((Efinal.image (localCellLabel C 0 (2^c) pA)).card:ℝ) ≤
      ((129^4:ℝ)*Cover)*(6/sigma) := by
    rw [hSupportRead]
    exact hSupport.trans (mul_le_mul_of_nonneg_left hTime (mul_nonneg (by positivity) hCover))
  have hRatio : (6*(64/((2^depth:ℕ):ℝ)))/((Rd:ℝ)*mu m)=6/sigma := by
    rw [hwidth,hRdMesh]
    dsimp [sigma]
    have hN : (((2^c:ℕ):ℝ)) ≠ 0 := by positivity
    field_simp [hN,hC.1.2.1.ne']
  have hCoverEq : (129^4:ℝ)*Cover=unionConstant K*sigma^(-(3-extremalExponent)) := by
    dsimp only [Cover,unionConstant]
    rw [hRatio,Real.div_rpow (by norm_num : (0:ℝ) ≤ 6) hs.le,Real.rpow_neg hs.le]
    have hp : (6:ℝ)^(3-extremalExponent)*(6:ℝ)^(3-extremalExponent)=
        (36:ℝ)^(3-extremalExponent) := by
      rw [←Real.mul_rpow (by norm_num : (0:ℝ) ≤ 6) (by norm_num : (0:ℝ) ≤ 6)]
      norm_num
    calc
      _ = ((129^4:ℝ)*(257^4:ℝ)*(9^3:ℝ)*(13^3:ℝ)^2*K^2)*
          ((6:ℝ)^(3-extremalExponent)*(6:ℝ)^(3-extremalExponent))/sigma^(3-extremalExponent) := by ring
      _ = _ := by rw [hp]; ring
  have hBalance : sigma^(-(3-extremalExponent))*sigma^3=sigma^extremalExponent := by
    rw [←Real.rpow_natCast sigma 3,←Real.rpow_add hs]
    congr 1
    ring
  have hscalar : (((129^4:ℝ)*Cover)*(6/sigma))*(sigma/2)^4 ≤
      unionConstant K*sigma^extremalExponent := by
    rw [hCoverEq]
    have he : (6/sigma)*(sigma/2)^4=(3/8:ℝ)*sigma^3 := by field_simp [hs.ne']; ring
    calc
      _ = unionConstant K*(sigma^(-(3-extremalExponent))*sigma^3)*(3/8:ℝ) := by
        rw [mul_assoc,mul_assoc,he]
        ring
      _ = unionConstant K*sigma^extremalExponent*(3/8:ℝ) := by rw [hBalance]
      _ ≤ _ := mul_le_of_le_one_right (by unfold unionConstant; positivity) (by norm_num)
  have hVolReal := (mul_le_mul_of_nonneg_right hCount (show 0 ≤ (sigma/2)^4 by positivity)).trans hscalar
  rw [NativeLocalParentSource.source_union_volume hC univ Efinal 0 c pA hParentFinal]
  have he : ((2^c:ℕ):ℝ)*C.thickness/128=sigma/2 := by dsimp [sigma]; ring
  rw [he]
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_pow (half_pos hs).le,
    ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hVolReal

end NativeRememberedSourceUnion

end -- anonymous noncomputable section of native_remembered_source_union

/- Source unit: native_remembered_height_selection
   Original SHA256: b82d839ce63eda2313767be0bf09929963b27bc7a0e490bd8d0a41ff3645cd63 -/
/- UNVERIFIED actual remembered-height selection. The height capacity is
read from original configured points and literal intermediate shadow cells.
No per-bin height-count certificate is supplied to the public selector. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeRememberedHeightSelection
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalCellChartGeometry NativeLocalParentSource
open NativeLocalParentCells NativeLocalCellCoherence NativeRelativeCoarseReadback
open NativeRelativeParentLabels NativeTranslatedGrainHeightOverlap
open NativeMatchedShadowConfiguredGeometry NativeRememberedSourceMaps
open NativeReferenceXYGridPoints NativeHorizontalGrainSlice CanonicalConfiguredE4Bridge

/-- Exact height error read from the actual representative shadow. -/
theorem occurrence_shadow_height {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (backbone : Finset (Fin n)) (m b : ℕ) (hm : 6 ≤ m) (p : Parent)
    (hp : (parentLabels D backbone a (2^m) p).Nonempty)
    (hNscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (hRelScale : ((2^m:ℕ):ℝ)*D.thickness*((2^b:ℕ):ℝ) ≤ 64)
    (Q : Finset Parent) (C : FiniteScaleSource Q.card)
    (hthickness : C.thickness=64/((2^b:ℕ):ℝ))
    (cells : Fin Q.card → Finset Index)
    (A : Finset (Fin n × Index)) (hA : A⊆incidences original)
    (hparent : ∀z∈A,z.1∈parentLabels D backbone a (2^m) p)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀t i j,|F t i j| ≤ 1/4) (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ) ≤ 4096/((2^b:ℕ):ℝ))
    (z : (Fin Q.card × Index) × (Fin n × Index))
    (hz : z∈occurrences h backbone a m b p hp Q cells A) :
    |NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2.2 (3:Fin 4)-
      cellCenter (mesh C) z.1.2 (3:Fin 4)| ≤ 2*C.thickness := by
  obtain ⟨_hzCells,hzA,_hphase,hshadow⟩ :=
    (mem_occurrences h backbone a m b p hp Q cells A z).mp hz
  have horig : z.2.2∈original z.2.1 := (mem_incidences original _ _).mp (hA hzA)
  have hi := (mem_parentLabels D backbone a (2^m) p _).mp (hparent z.2 hzA)
  let rep := originalRepresentative h backbone a m p hp (2^b)
    (relativeLabel D a (2^m) p (2^b) z.2.1)
  have hr := originalRepresentative_label h backbone a m p hp (2^b) z.2.1 (hparent z.2 hzA)
  have hn := point_shadow_center_distance h original horiginal ha m (2^b) hm (by positivity)
    hNscale hRelScale p z.2.1 rep z.2.2 horig hi.2 hr s P hP hd F Fcfg hF hCfg
    R0 hR0 hbase hmatch
  have hcoord := (PiLp.dist_apply_le
    (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2.2)
    (NativePackedFrameIsometry.frame s P hP hd
      (cellCenter (32/((2^b:ℕ):ℝ))
        (NativeRelativeCoarsePointMenu.doubleLabel D a (2^m) (2^b) p rep z.2.1 z.2.2)))
    (3:Fin 4)).trans hn
  rw [NativePackedFrameIsometry.frame_height,Real.dist_eq] at hcoord
  change |NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2.2 (3:Fin 4)-
    cellCenter (C.thickness/2) z.1.2 (3:Fin 4)| ≤ 2*C.thickness
  rw [hthickness,hshadow]
  change |NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2.2 (3:Fin 4)-
    cellCenter ((64/((2^b:ℕ):ℝ))/2)
      (NativeRelativeCoarsePointMenu.doubleLabel D a (2^m) (2^b) p rep z.2.1 z.2.2) (3:Fin 4)| ≤ _
  have he : (64/((2^b:ℕ):ℝ))/2=32/((2^b:ℕ):ℝ) := by ring
  rw [he]
  exact hcoord

/-- The known configured-height lattice bounds one actual local time-bin.
A chosen occurrence is kept for each old point; other antecedents are irrelevant. -/
theorem occurrence_heights_per_bin {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (backbone : Finset (Fin n)) (m b : ℕ) (hm : 6 ≤ m) (p : Parent)
    (hp : (parentLabels D backbone a (2^m) p).Nonempty)
    (hNscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (hRelScale : ((2^m:ℕ):ℝ)*D.thickness*((2^b:ℕ):ℝ) ≤ 64)
    (Q : Finset Parent) (C : FiniteScaleSource Q.card)
    (hthickness : C.thickness=64/((2^b:ℕ):ℝ))
    (cells : Fin Q.card → Finset Index)
    (A : Finset (Fin n × Index)) (hA : A⊆incidences original)
    (hparent : ∀z∈A,z.1∈parentLabels D backbone a (2^m) p)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀t i j,|F t i j| ≤ 1/4) (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ) ≤ 4096/((2^b:ℕ):ℝ))
    (eps : ℝ) (heps : 0 < eps) (hmesh : mu m*(R0:ℝ)=64*eps)
    (c : ℕ) (pA : Parent)
    (hdscale : C.thickness ≤ ((2^c:ℕ):ℝ)*C.thickness/64)
    (hepsScale : eps ≤ ((2^c:ℕ):ℝ)*C.thickness/64)
    (V : Finset ((Fin Q.card × Index) × (Fin n × Index)))
    (hVO : V⊆occurrences h backbone a m b p hp Q cells A)
    (j : ℤ) (hbin : ∀z∈V,finalTime (taggedKey D a m C c pA z)=j) :
    ((V.image (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0
      z.2.2 (3:Fin 4))).card:ℝ) ≤ 4096*((((2^c:ℕ):ℝ)*C.thickness/64)/eps) := by
  have hC : 0 < C.thickness := by rw [hthickness]; positivity
  by_cases hV : V.Nonempty
  · obtain ⟨z0,_hz0⟩ := hV
    let S := V.image (fun z => z.2.2)
    have hWitness (k : Index) (hk : k∈S) :
        ∃z∈V,z.2.2=k := mem_image.mp hk
    let chosen : Index → ((Fin Q.card × Index) × (Fin n × Index)) :=
      fun k => if hk : k∈S then Classical.choose (hWitness k hk) else z0
    have hchosen (k : Index) (hk : k∈S) : chosen k∈V ∧ (chosen k).2.2=k := by
      simp only [chosen,dif_pos hk]
      exact Classical.choose_spec (hWitness k hk)
    have hnear (k : Index) (hk : k∈S) :
        |NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 k (3:Fin 4)-
          cellCenter (mesh C) (chosen k).1.2 (3:Fin 4)| ≤ 2*C.thickness := by
      obtain ⟨hv,he⟩ := hchosen k hk
      have hn := occurrence_shadow_height h original horiginal ha backbone m b hm p hp hNscale hRelScale
        Q C hthickness cells A hA hparent s P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
        (chosen k) (hVO hv)
      simpa only [he] using hn
    have htime (k : Index) (hk : k∈S) :
        cellLabel C 0 (2^c) pA (chosen k).1.1 (chosen k).1.2 (3:Fin 4)=j :=
      hbin (chosen k) (hchosen k hk).1
    have hcap := NativeRememberedHeightGeometry.actual_old_heights_per_bin
      D a m p s P hP hd F Fcfg R0 hR0 eps heps hmesh C hC (2^c) (by positivity) pA j
      S (fun k => (chosen k).1.2) (fun k => (chosen k).1.1) htime hnear hdscale hepsScale
    have himage : S.image (fun k => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 k (3:Fin 4))=
        V.image (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2.2 (3:Fin 4)) := by
      dsimp only [S]
      rw [image_image]
      rfl
    rw [himage] at hcap
    exact hcap
  · have he : V=∅ := not_nonempty_iff_eq_empty.mp hV
    rw [he,image_empty,card_empty,Nat.cast_zero]
    positivity

/-- Select one genuine original translated height in every final local bin.
All capacities are derived from the literal source maps and the frozen baseline. -/
theorem select_actual_old_height {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (backbone : Finset (Fin n)) (m b : ℕ) (hm : 6 ≤ m) (p : Parent)
    (hp : (parentLabels D backbone a (2^m) p).Nonempty)
    (hNscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (hRelScale : ((2^m:ℕ):ℝ)*D.thickness*((2^b:ℕ):ℝ) ≤ 64)
    (Q : Finset Parent) (C : FiniteScaleSource Q.card)
    (hthickness : C.thickness=64/((2^b:ℕ):ℝ))
    (cells : Fin Q.card → Finset Index)
    (A : Finset (Fin n × Index)) (hA : A⊆incidences original)
    (hparent : ∀z∈A,z.1∈parentLabels D backbone a (2^m) p)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀t i j,|F t i j| ≤ 1/4) (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ) ≤ 4096/((2^b:ℕ):ℝ))
    (eps : ℝ) (heps : 0 < eps) (hmesh : mu m*(R0:ℝ)=64*eps)
    (c : ℕ) (pA : Parent)
    (hdscale : C.thickness ≤ ((2^c:ℕ):ℝ)*C.thickness/64)
    (hepsScale : eps ≤ ((2^c:ℕ):ℝ)*C.thickness/64)
    (T : Finset (Fin n × Index)) (hAT : A⊆T)
    (Hsingle : ∀x∈T,∀y∈T,translatedHeight D a m x.2/((8*R0:ℕ):ℤ)=
      translatedHeight D a m y.2/((8*R0:ℕ):ℤ) → translatedHeight D a m x.2=translatedHeight D a m y.2) :
    let O := occurrences h backbone a m b p hp Q cells A
    ∃B⊆O.image (taggedKey D a m C c pA),
      ((O.image (taggedKey D a m C c pA)).card:ℝ) ≤
        (4096*((((2^c:ℕ):ℝ)*C.thickness/64)/eps))*
          ((selectedPairs D a m C c pA O B).image (localPair C 0 (2^c) pA)).card ∧
      (∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1) ∧
      (selectedPairs D a m C c pA O B).image (localPair C 0 (2^c) pA)=B.image Prod.snd := by
  intro O
  apply select_old_height D a m C c pA O (by rw [hthickness]; positivity)
  intro j
  have hOT (z : (Fin Q.card × Index) × (Fin n × Index)) (hz : z∈O) : z.2∈T :=
    hAT ((mem_occurrences h backbone a m b p hp Q cells A z).mp hz).2.1
  rw [tagged_height_card_eq_physical D a m C c pA p T O hOT s P hP hd F Fcfg R0 hR0 Hsingle j]
  exact occurrence_heights_per_bin h original horiginal ha backbone m b hm p hp hNscale hRelScale
    Q C hthickness cells A hA hparent s P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
    eps heps hmesh c pA hdscale hepsScale
    (O.filter (fun z => finalTime (taggedKey D a m C c pA z)=j)) (filter_subset _ _) j
    (fun z hz => (mem_filter.mp hz).2)

end NativeRememberedHeightSelection

end -- anonymous noncomputable section of native_remembered_height_selection

/- Source unit: native_remembered_occurrence_readback
   Original SHA256: f2578d7c12d524f8816b0721984b4d2746cfe7013e99ddedd1b9628391915c08 -/
/- UNVERIFIED literal same-reference row and occurrence readback.
The selected intermediate source keeps the original sparse T rows. Later
old-phase restrictions are made on the unchanged original witnesses. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeRememberedOccurrenceReadback
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeLocalParentSource NativeRelativeCoarseReadback
open NativeRelativeParentLabels NativeRememberedSourceMaps NativeIntermediateParentPopulation
open NativeCoarseCellSource NativeCoarseDirectionThinning NativeCoarseSourceParentReadback
open NativeJointKeyDescent

section Actual
variable {n : ℕ} {D : FiniteScaleSource n} {eta etaRef a : ℝ}
  (h : IsWangZakharovNativeFiniteInput D eta) (backbone : Finset (Fin n))
  (Eref T : Finset (Fin n × Index)) (level m b : ℕ) (p : Parent)
  (hp : (parentLabels D backbone a (2^m) p).Nonempty)
  (hRef : IsWangZakharovNativeFiniteInput (NativeLocalParentSource.source h backbone Eref a m p) etaRef)

/-- These are the literal finite rows of the actual same-Q coarse source. -/
def actualRows (Q : Finset Parent) : Fin Q.card → Finset Index :=
  intermediateCells (D:=NativeLocalParentSource.source h backbone Eref a m p)
    0 (level-m+6) b Q (representative hRef univ 0 (2^b))
    (incidences (sourceCells D backbone T a (2^m) p))

/-- Exact finite row identity, stronger than equality of the shaded unions. -/
theorem actual_rows_readback
    (hT : ∀z∈T,z.1∈parentLabels D backbone a (2^m) p)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m≤level) (hb : b≤level-m+6)
    (Q : Finset Parent) (i : Fin Q.card) :
    actualRows h backbone Eref T level m b p hRef Q i=
      (((T.image (doublePair h backbone a m p hp (2^b))).filter
        (fun z => z.1=parentIndex Q i)).image Prod.snd) := by
  have hc := NativeCurrentReferenceReadback.selected_relative_incidence_image
    h backbone Eref T a m p hp (2^b) (NativeCoarseDyadicShading.block (level-m+6) b) hT hRef
    (NativeCoarseDyadicShading.block_mesh (local_source_dyadic h backbone Eref a level m p hdy hm) hb)
  unfold actualRows intermediateCells NativeCoarseShadingCapacity.rows
  rw [hc]

/-- Every retained original witness in Q has a genuine intermediate row
occurrence, and there are no other original witnesses in the occurrence image. -/
theorem original_image
    (hT : ∀z∈T,z.1∈parentLabels D backbone a (2^m) p)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m≤level) (hb : b≤level-m+6)
    (Q : Finset Parent) (A : Finset (Fin n × Index)) (hAT : A⊆T) :
    (occurrences h backbone a m b p hp Q (actualRows h backbone Eref T level m b p hRef Q) A).image Prod.snd=
      NativeSameQSourceRestriction.restrict D a m b p Q A := by
  ext z
  constructor
  · intro hz
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hz
    obtain ⟨_hvRows,hvA,hphase,_hcell⟩ := (mem_occurrences h backbone a m b p hp Q _ A v).mp hv
    apply mem_filter.mpr
    refine ⟨hvA,?_⟩
    rw [←hphase]
    exact parentIndex_mem Q v.1.1
  · intro hz
    obtain ⟨hzA,hzQ⟩ := mem_filter.mp hz
    have hrange : relativeLabel D a (2^m) p (2^b) z.1∈Set.range (parentIndex Q) := by
      rw [parentIndex_range]
      exact hzQ
    obtain ⟨i,hi⟩ := hrange
    let k := (doublePair h backbone a m p hp (2^b) z).2
    have hk : k∈actualRows h backbone Eref T level m b p hRef Q i := by
      rw [actual_rows_readback h backbone Eref T level m b p hp hRef hT hdy hm hb Q i]
      refine mem_image.mpr ⟨doublePair h backbone a m p hp (2^b) z,
        mem_filter.mpr ⟨mem_image_of_mem _ (hAT hzA),?_⟩,rfl⟩
      exact hi.symm
    refine mem_image.mpr ⟨((i,k),z),?_,rfl⟩
    apply (mem_occurrences h backbone a m b p hp Q _ A _).mpr
    exact ⟨(mem_incidences _ _ _).mpr hk,hzA,hi,rfl⟩

/-- An original w-phase occurrence is in the corresponding ACTUAL current
parent, whose intercept label is divided by512. This derives the current
parent condition from Q's actual representatives and dyadic ancestry. -/
theorem occurrence_current_parent
    (Q : Finset Parent)
    (hQ : Q⊆(univ : Finset (Fin (parentLabels D backbone a (2^m) p).card)).image
      (parentLabel (NativeLocalParentSource.source h backbone Eref a m p) 0 (2^b)))
    (hsep : ∀q∈Q,∀q'∈Q,q≠q' → 64/((2^b:ℕ):ℝ) ≤
      dist (direction ((NativeLocalParentSource.source h backbone Eref a m p).line
        (representative hRef univ 0 (2^b) q)))
      (direction ((NativeLocalParentSource.source h backbone Eref a m p).line
        (representative hRef univ 0 (2^b) q'))))
    (A : Finset (Fin n × Index)) (c : ℕ) (hc : c≤b) (qOld : Parent)
    (hphase : ∀z∈A,relativeLabel D a (2^m) p (2^c) z.1=qOld) :
    let C := NativeCoarseCellSource.source hRef 0 (level-m+6) b Q
      (representative hRef univ 0 (2^b)) (incidences (sourceCells D backbone T a (2^m) p)) hsep
    ∀z∈occurrences h backbone a m b p hp Q (actualRows h backbone Eref T level m b p hRef Q) A,
      parentLabel C 0 (2^c) z.1.1=zeroProjection qOld := by
  intro C z hz
  obtain ⟨_hzRows,hzA,hzPhase,_hzCell⟩ := (mem_occurrences h backbone a m b p hp Q _ A z).mp hz
  have hrep : ∀q∈Q,parentLabel (NativeLocalParentSource.source h backbone Eref a m p) 0 (2^b)
      (representative hRef univ 0 (2^b) q)=q :=
    fun q hq => (representative_spec hRef univ 0 (2^b) (hQ hq)).2
  rw [NativeIntermediateParentPopulation.parent_from_ancestor hRef 0 (level-m+6) b Q
    (representative hRef univ 0 (2^b)) (incidences (sourceCells D backbone T a (2^m) p))
    hsep hrep c hc z.1.1,hzPhase,relative_ancestor D a (2^m) p b c hc z.2.1,hphase z.2 hzA]

end Actual
end NativeRememberedOccurrenceReadback

end -- anonymous noncomputable section of native_remembered_occurrence_readback

/- Source unit: native_remembered_fine_count
   Original SHA256: f521eff0e02070ae50fe02d3d5bf52e9cab26065f4d851a7790a537420935cd5 -/
/- UNVERIFIED same-baseline fine graph to remembered tagged-image bound.
The final local pair keeps its literal intermediate tube index. A tagged
fiber therefore lies in one true old height and one old b-parent, and the
actual fixed-height tube/point bound supplies its capacity. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeRememberedFineCount
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeLocalParentSource NativeRelativeCoarseReadback
open NativeRelativeParentLabels NativeRememberedSourceMaps NativeRememberedOccurrenceReadback
open NativeReferenceXYGridPoints NativeHorizontalGrainSlice CanonicalConfiguredE4Bridge
open NativeConfiguredIncidenceFibers NativeCappedOldAncestors NativeActualFineWeightShadingBridge
open NativeFineWeightedCoarseCore
open NativeTranslatedGrainHeightOverlap

/-- The full reference population is derived from the original backbone.
The original graph stays at b0 even when the intermediate source is at b.
No output count, height-richness, or native input for sparse A is assumed. -/
theorem fine_graph_le_tagged {n : ℕ} {D : FiniteScaleSource n} {eta etaS a zeta pExp : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (Eref T : Finset (Fin n × Index))
    (level m b0 b : ℕ) (hm : 6 ≤ m) (hb0 : 8 ≤ b0) (hb : b≤b0)
    (HB : NativeMiddleWindowBalance.HasOriginalBackbone D original R a level zeta)
    (hmb0 : m+b0≤level) (hscale : D.thickness≤(rho m)^2) (p : Parent)
    (hp : (parentLabels D R a (2^m) p).Nonempty)
    (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (hbudget : (64:ℝ)^3*(source h R Eref a m p).thickness^pExp≤D.thickness^zeta)
    (hT : T⊆incidences original)
    (hparent : ∀z∈T,z.1∈parentLabels D R a (2^m) p)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hdim : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀t i j,|F t i j|≤1/4) (hCfg : ∀t i j,|Fcfg t i j|≤1/4)
    (R0 : ℕ) (hR0 : 0<R0) (hbase : rho m≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ)=4096/((2^b0:ℕ):ℝ))
    (Q : Finset Parent) (C : FiniteScaleSource Q.card) (c : ℕ) (pA : Parent)
    (A : Finset (Fin n × Index)) (hAT : A⊆T)
    (hAQ : ∀z∈A,relativeLabel D a (2^m) p (2^b) z.1∈Q) :
    let cfg := NativeActualConfiguredPoint.point D a m p s P hP hdim F Fcfg R0
    (∀x∈T.image (fun z => cfg z.2),∀y∈T.image (fun z => cfg z.2),x≠y →
      64/((2^b0:ℕ):ℝ)≤dist x y) →
    let cells := actualRows h R Eref T level m b p hS Q
    let Occ := occurrences h R a m b p hp Q cells A
    ((NativeSameQFineGraph.graph h R Eref a m b0 p hS cfg A).card:ℝ) ≤
      fineCapacity*(source h R Eref a m p).thickness^(-pExp)*
        ((64/((2^b:ℕ):ℝ))/(64/((2^b0:ℕ):ℝ)))^3*
          ((Occ.image (taggedKey D a m C c pA)).card:ℝ) := by
  intro cfg hpointSep cells Occ
  let Sref := source h R Eref a m p
  let eps : ℝ := 64/((2^b0:ℕ):ℝ)
  let d : ℝ := 64/((2^b:ℕ):ℝ)
  let O := NativePackedFrameIsometry.frame s P hP hdim
  let pair := fun z : Fin n × Index => (cfg z.2,outputTube h R Eref a m b0 p hS z.1)
  let G := T.image pair
  let selected := incidences (sourceCells D R T a (2^m) p)
  have hNle : ((2^b:ℕ):ℝ)≤((2^b0:ℕ):ℝ) := by
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) hb
  have hepsd : eps≤d := div_le_div_of_nonneg_left (by norm_num) (by positivity) hNle
  have hstep : 1/((2^b:ℕ):ℝ)≤d :=
    div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hRefScale : ((2^b0:ℕ):ℝ)*Sref.thickness≤1 :=
    NativeSameReferenceChartBounds.source_scale_guard (a:=a) h R Eref level m b0 p HB.2.1 hmb0
  have Hprofile := NativeSameReferenceChartBounds.population_through h original R level HB Eref m b0 hmb0 p hbudget
  have Hfine : ∀q : Parent,
      ((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).filter
        (fun i => parentLabel Sref 0 (2^b0) i=q)).Nonempty →
      Sref.thickness^pExp*((1/((2^b0:ℕ):ℝ))/Sref.thickness)^3≤
        (((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).filter
          (fun i => parentLabel Sref 0 (2^b0) i=q)).card:ℝ) :=
    fun q hq => (Hprofile ⟨b0,by omega⟩ q hq).1
  have hGgeom : ∀x i,(x,i)∈G → x∈markedUnitTube
      (MarkedIsometricChart.line O 0
        ((NativeFullCoarseShadow.fullSource hS univ 0 (level-m+6) b0 selected).line i)) eps := by
    intro x i hxi
    obtain ⟨z,hz,hzi⟩ := mem_image.mp hxi
    have hk : (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p)
        (localIndex h R Eref a m p hS z.1),z.2)∈incidences original := by
      rw [localIndex_readback h R Eref a m p hS z.1 (hparent z hz)]
      exact hT hz
    have hh := NativeActualConfiguredTube.point_mem_full_tube h original horiginal ha R Eref m hm
      hscale p hS (level-m+6) b0 selected (localIndex h R Eref a m p hS z.1) z.2 hk
      s P hP hdim F Fcfg hF hCfg R0 hR0 hbase hmatch.le
    have hx : cfg z.2=x := congrArg Prod.fst hzi
    have hi : outputTube h R Eref a m b0 p hS z.1=i := congrArg Prod.snd hzi
    rw [←hx,←hi]
    exact hh
  have hGpoints : G.image Prod.fst=T.image (fun z => cfg z.2) := by
    dsimp only [G]
    rw [image_image]
    rfl
  have hGsep : ∀x∈G.image Prod.fst,∀y∈G.image Prod.fst,x≠y → eps≤dist x y := by
    rw [hGpoints]
    exact hpointSep
  have hOrig : Occ.image Prod.snd=A := by
    rw [original_image h R Eref T level m b p hp hS hparent HB.2.1
      (by omega) (by omega) Q A hAT]
    exact filter_eq_self.mpr hAQ
  have hImage : Occ.image (fun z => pair z.2)=A.image pair := by
    rw [←hOrig,image_image]
    rfl
  change ((A.image pair).card:ℝ)≤_
  rw [←hImage]
  apply NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images Occ
    (fun z => pair z.2) (taggedKey D a m C c pA)
  intro v _hv
  let V := Occ.filter (fun z => taggedKey D a m C c pA z=v)
  let time := NativeConfiguredTimeCoarsening.finalTime (mu m*(R0:ℝ)) (v.1/((8*R0:ℕ):ℤ))
  have hsub : V.image (fun z => pair z.2)⊆G.filter
      (fun z => z.1 (3:Fin 4)=time ∧ oldAncestor Sref univ 0 b0 b z.2=NativeCoarseCellSource.parentIndex Q v.2.1) := by
    intro u hu
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hu
    obtain ⟨hzO,hzKey⟩ := mem_filter.mp hz
    obtain ⟨_hzCell,hzA,hzPhase,_hshadow⟩ := (mem_occurrences h R a m b p hp Q cells A z).mp hzO
    have hheight : translatedHeight D a m z.2.2=v.1 := congrArg Prod.fst hzKey
    have htube : z.1.1=v.2.1 := congrArg (fun w : ℤ × (Fin Q.card × Index) => w.2.1) hzKey
    refine mem_filter.mpr ⟨mem_image_of_mem _ (hAT hzA),?_,?_⟩
    · change cfg z.2.2 (3:Fin 4)=time
      dsimp only [cfg,time]
      rw [NativeActualConfiguredPoint.point,NativeActualConfiguredPoint.graphGrid_height,
        NativeActualConfiguredPoint.sourceLabel_height,hheight]
    · change oldAncestor Sref univ 0 b0 b (outputTube h R Eref a m b0 p hS z.2.1)=_
      dsimp only [oldAncestor,Sref]
      rw [outputTube_ancestor_readback h R Eref a m b0 b hb p hS z.2.1 (hparent z.2 (hAT hzA)),←hzPhase,htube]
  have hcap := NativeFixedHeightPairCap.full_source_old_parent_height_fiber (a:=0) (e:=pExp)
    hS univ (level-m+6) b0 hb0 selected hRefScale Hfine O
    (NativePackedFrameIsometry.frame_height s P hP hdim) G hGgeom hGsep b hb hepsd hstep
    time (NativeCoarseCellSource.parentIndex Q v.2.1)
  exact (show ((V.image (fun z => pair z.2)).card:ℝ)≤
    ((G.filter (fun z => z.1 (3:Fin 4)=time ∧
      oldAncestor Sref univ 0 b0 b z.2=NativeCoarseCellSource.parentIndex Q v.2.1)).card:ℝ) by
      exact_mod_cast card_le_card hsub).trans hcap

end NativeRememberedFineCount

end -- anonymous noncomputable section of native_remembered_fine_count
