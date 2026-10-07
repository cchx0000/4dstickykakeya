/- UNVERIFIED actual remembered-height selection. The height capacity is
read from original configured points and literal intermediate shadow cells.
No per-bin height-count certificate is supplied to the public selector. -/
import Theorems.Thm_StickyKakeya4_native_remembered_source_maps
import Theorems.Thm_StickyKakeya4_native_remembered_height_geometry
import Theorems.Thm_StickyKakeya4_native_matched_shadow_configured_geometry

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
      rw [S,image_image]
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
