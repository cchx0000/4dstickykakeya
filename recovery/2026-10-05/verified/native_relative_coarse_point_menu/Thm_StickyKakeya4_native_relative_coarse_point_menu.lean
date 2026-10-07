import Theorems.Thm_StickyKakeya4_native_relative_coarse_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeRelativeCoarsePointMenu
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeOriginalCellChartGeometry
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeLocalParentGeometry
open NativeRelativeParentLabels NativeRelativeCoarseGeometry NativeLocalParentSource
open scoped BigOperators

def localMesh {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) : ℝ := (N:ℝ)*D.thickness/128

def roundedHeight {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (p : Parent)
    (i : Fin n) (k : Index) : ℝ :=
  cellCenter (localMesh D N) (NativeLocalParentCells.cellLabel D a N p i k) (3:Fin 4)

/-- Literal local fine-cell rounding followed by relative coarse projection
to the chosen relative representative's actual line. -/
def doubleFront {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (p : Parent)
    (j i : Fin n) (k : Index) : E4 :=
  zeroGraphPoint (NativeLocalParentGeometry.line D a N p j) (roundedHeight D a N p i k)

def doubleLabel {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N M : ℕ) (p : Parent)
    (j i : Fin n) (k : Index) : Index :=
  wzDyadicCellIndex (32/(M:ℝ)) (doubleFront D a N p j i k)

def globalLabel {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (K : ℕ)
    (j : Fin n) (k : Index) : Index :=
  wzDyadicCellIndex (32/(K:ℝ)) (NativeOriginalPaddedCells.frontPoint D a (0,0) j k)

def pointMenu (N K M : ℕ) (p : Parent) (q : Index) : Finset Index :=
  let center := bridgePoint N p (cellCenter (32/(K:ℝ)) q)
  Fintype.piFinset (fun v => Icc (⌊center v/(32/(M:ℝ))⌋-1) (⌊center v/(32/(M:ℝ))⌋+1))

lemma pointMenu_card (N K M : ℕ) (p : Parent) (q : Index) :
    (pointMenu N K M p q).card = 81 := by
  have hi (v : Fin 4) :
      (Icc (⌊bridgePoint N p (cellCenter (32/(K:ℝ)) q) v/(32/(M:ℝ))⌋-1)
        (⌊bridgePoint N p (cellCenter (32/(K:ℝ)) q) v/(32/(M:ℝ))⌋+1)).card = 3 := by
    have hh : ((Icc (⌊bridgePoint N p (cellCenter (32/(K:ℝ)) q) v/(32/(M:ℝ))⌋-1)
        (⌊bridgePoint N p (cellCenter (32/(K:ℝ)) q) v/(32/(M:ℝ))⌋+1)).card : ℤ) = 3 := by
      rw [Int.card_Icc_of_le _ _ (by omega)]
      omega
    exact_mod_cast hh
  simp [pointMenu,Fintype.card_piFinset,hi]

lemma rounded_height_error {n : ℕ} {D : FiniteScaleSource n} (hd : 0 < D.thickness)
    (a : ℝ) (N : ℕ) (hN : 0 < N) (p : Parent) (i : Fin n) (k : Index) :
    |roundedHeight D a N p i k-NativeLocalParentCells.frontPoint D a N p i k (3:Fin 4)| ≤
      localMesh D N/2 := by
  exact cell_center_coordinate_error (by unfold localMesh; positivity)
    (NativeLocalParentCells.frontPoint D a N p i k) 3

lemma rounded_height_bound {n : ℕ} {D : FiniteScaleSource n} (hd : 0 < D.thickness)
    (a : ℝ) (N : ℕ) (hN : 0 < N) (hscale : (N:ℝ)*D.thickness ≤ 1)
    (p : Parent) (i : Fin n) (k : Index) (ht : |NativeOriginalPaddedCells.oldTime D a k| ≤ 1) :
    |roundedHeight D a N p i k| ≤ 4 := by
  have herr := rounded_height_error hd a N hN p i k
  have hf : |NativeLocalParentCells.frontPoint D a N p i k (3:Fin 4)| ≤ 1/128 := by
    rw [NativeLocalParentCells.frontPoint_height,abs_div,
      abs_of_pos (by norm_num : (0:ℝ)<128)]
    exact div_le_div_of_nonneg_right ht (by norm_num)
  have hh := (abs_add_le
    (roundedHeight D a N p i k-NativeLocalParentCells.frontPoint D a N p i k (3:Fin 4))
    (NativeLocalParentCells.frontPoint D a N p i k (3:Fin 4))).trans (add_le_add herr hf)
  simp only [sub_add_cancel,localMesh] at hh
  linarith

lemma bridge_representative_error {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N K : ℕ) (hK : 0 < K) (p : Parent) (i j : Fin n) (k : Index)
    (hp : parentLabel D a K j=parentLabel D a K i)
    (ht : |NativeOriginalPaddedCells.oldTime D a k| ≤ 1) (v : Fin 4) :
    |bridgePoint N p (NativeOriginalPaddedCells.frontPoint D a (0,0) i k) v-
      bridgePoint N p (NativeOriginalPaddedCells.frontPoint D a (0,0) j k) v| ≤
        (N:ℝ)/(32768*(K:ℝ)) := by
  refine Fin.lastCases ?_ (fun u => ?_) v
  · change |NativeOriginalPaddedCells.frontPoint D a (0,0) i k (3:Fin 4)/512-
      NativeOriginalPaddedCells.frontPoint D a (0,0) j k (3:Fin 4)/512| ≤ _
    rw [NativeOriginalPaddedCells.frontPoint_height,NativeOriginalPaddedCells.frontPoint_height]
    simp only [sub_self,abs_zero]
    positivity
  · have hid :
        bridgePoint N p (NativeOriginalPaddedCells.frontPoint D a (0,0) i k) u.castSucc-
          bridgePoint N p (NativeOriginalPaddedCells.frontPoint D a (0,0) j k) u.castSucc =
        (N:ℝ)*(NativeOriginalPaddedCells.frontPoint D a (0,0) i k u.castSucc-
          NativeOriginalPaddedCells.frontPoint D a (0,0) j k u.castSucc)/512 := by
      simp only [bridgePoint,ActualSlopeSource.heightPoint_castSucc,
        NativeOriginalPaddedCells.frontPoint_height]
      ring
    rw [hid,abs_div,abs_mul,abs_of_nonneg (Nat.cast_nonneg N),
      abs_of_pos (by norm_num : (0:ℝ)<512)]
    have hh := NativeCoarsePointMultiplicity.same_parent_front_error D a K hK i j k hp ht u.castSucc
    rw [abs_sub_comm] at hh
    calc
      _ ≤ ((N:ℝ)*((1/(K:ℝ))/64))/512 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg N)) (by norm_num)
      _ = _ := by ring

/-- Complete forward error estimate for the actual double map. K=NM/64 is
the original global parent scale; its cube mesh is 2048/(NM). -/
theorem double_front_center_error {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (N K M : ℕ) (hN : 0 < N) (hK : 0 < K) (hM : 0 < M)
    (hKM : (K:ℝ)*64=(N:ℝ)*(M:ℝ))
    (hNscale : (N:ℝ)*D.thickness ≤ 1) (hKscale : (K:ℝ)*D.thickness ≤ 1)
    (p : Parent) (i jg jr : Fin n) (k : Index)
    (hip : parentLabel D a N i=p)
    (hg : parentLabel D a K jg=parentLabel D a K i)
    (hr : relativeLabel D a N p M jr=relativeLabel D a N p M i)
    (ht : |NativeOriginalPaddedCells.oldTime D a k| ≤ 1) (v : Fin 4) :
    |doubleFront D a N p jr i k v-
      bridgePoint N p (cellCenter (32/(K:ℝ)) (globalLabel D a K jg k)) v| ≤ 32/(M:ℝ) := by
  have hd := h.1.2.1
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hKr : (0:ℝ)<K := by exact_mod_cast hK
  have hratio : (N:ℝ)/(K:ℝ)=64/(M:ℝ) := by
    apply (div_eq_div_iff hKr.ne' hMr.ne').mpr
    nlinarith only [hKM]
  have hNd : (N:ℝ)*D.thickness ≤ 64/(M:ℝ) := by
    apply (le_div_iff₀ hMr).mpr
    have hprod := congrArg (fun x : ℝ => x*D.thickness) hKM
    nlinarith only [hKscale,hprod]
  have h1 := same_relative_front_error D a N M hM p i jr hr
    (roundedHeight D a N p i k) (rounded_height_bound hd a N hN hNscale p i k ht) v
  have h2 := zero_graph_time_error (NativeLocalParentGeometry.line D a N p i)
    (by intro u; rw [slope_line]; exact localSlope_bound D a N p i hip u)
    (roundedHeight D a N p i k) (NativeLocalParentCells.frontPoint D a N p i k (3:Fin 4)) v
  rw [local_front_bridge] at h2
  have h2' : |zeroGraphPoint (NativeLocalParentGeometry.line D a N p i) (roundedHeight D a N p i k) v-
      bridgePoint N p (NativeOriginalPaddedCells.frontPoint D a (0,0) i k) v| ≤ 1/(2048*(M:ℝ)) := by
    apply h2.trans
    calc
      _ ≤ (localMesh D N/2)/512 := div_le_div_of_nonneg_right (rounded_height_error hd a N hN p i k) (by norm_num)
      _ = ((N:ℝ)*D.thickness)/131072 := by unfold localMesh; ring
      _ ≤ (64/(M:ℝ))/131072 := div_le_div_of_nonneg_right hNd (by norm_num)
      _ = _ := by ring
  have h3 := bridge_representative_error D a N K hK p i jg k hg ht v
  have he3 : (N:ℝ)/(32768*(K:ℝ))=1/(512*(M:ℝ)) := by
    calc
      _ = ((N:ℝ)/(K:ℝ))/32768 := by ring
      _ = _ := by rw [hratio]; ring
  rw [he3] at h3
  have h4 := bridge_center_error N hN p
    (NativeLocalParentPhysicalMap.parent_slope_bound h N hN p i hip)
    (by positivity : (0:ℝ)<32/(K:ℝ)) (NativeOriginalPaddedCells.frontPoint D a (0,0) jg k) v
  have he4 : (N:ℝ)*(32/(K:ℝ))/256=8/(M:ℝ) := by
    calc
      _ = ((N:ℝ)/(K:ℝ))/8 := by ring
      _ = _ := by rw [hratio]; ring
  rw [he4] at h4
  have h12 := (abs_sub_le
    (doubleFront D a N p jr i k v)
    (zeroGraphPoint (NativeLocalParentGeometry.line D a N p i) (roundedHeight D a N p i k) v)
    (bridgePoint N p (NativeOriginalPaddedCells.frontPoint D a (0,0) i k) v)).trans (add_le_add h1 h2')
  have h123 := (abs_sub_le
    (doubleFront D a N p jr i k v)
    (bridgePoint N p (NativeOriginalPaddedCells.frontPoint D a (0,0) i k) v)
    (bridgePoint N p (NativeOriginalPaddedCells.frontPoint D a (0,0) jg k) v)).trans (add_le_add h12 h3)
  have h1234 := (abs_sub_le
    (doubleFront D a N p jr i k v)
    (bridgePoint N p (NativeOriginalPaddedCells.frontPoint D a (0,0) jg k) v)
    (bridgePoint N p (cellCenter (32/(K:ℝ)) (globalLabel D a K jg k)) v)).trans (add_le_add h123 h4)
  apply h1234.trans
  calc
    _ = (16421/2048:ℝ)/(M:ℝ) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) hMr.le

/-- Every literal original incidence has its relative double-map label in
an 81-cell menu determined solely by its global coarse cell and fixed parent. -/
theorem double_label_mem_menu {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N K M : ℕ) (hN : 0 < N) (hK : 0 < K) (hM : 0 < M)
    (hKM : (K:ℝ)*64=(N:ℝ)*(M:ℝ))
    (hNscale : (N:ℝ)*D.thickness ≤ 1) (hKscale : (K:ℝ)*D.thickness ≤ 1)
    (p : Parent) (i jg jr : Fin n) (k : Index) (hk : k∈original i)
    (hip : parentLabel D a N i=p)
    (hg : parentLabel D a K jg=parentLabel D a K i)
    (hr : relativeLabel D a N p M jr=relativeLabel D a N p M i) :
    doubleLabel D a N M p jr i k ∈ pointMenu N K M p (globalLabel D a K jg k) := by
  have ht := (NativeOriginalParentPhysicalData.original_cell_bounds h original horiginal a ha
    ((mem_incidences original i k).mpr hk)).1
  change |NativeOriginalPaddedCells.oldTime D a k| ≤ 1 at ht
  apply Fintype.mem_piFinset.mpr
  intro v
  exact NativeCoarseScaleInterpolation.floor_close (by positivity)
    _ _ (double_front_center_error h N K M hN hK hM hKM hNscale hKscale p i jg jr k hip hg hr ht v)

/-- Readback of the double map against the ACTUAL local source's coarse
projectedLabel, for every existing source index and relative representative. -/
lemma doubleLabel_eq_source_projected {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent) (M B : ℕ)
    (hmesh : (B:ℝ)*(source h R E a m p).thickness/128=32/(M:ℝ))
    (i j : Fin (parentLabels D R a (2^m) p).card) (k : Index) :
    doubleLabel D a (2^m) M p
      (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p) j)
      (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p) i) k =
    NativeCoarseShadingCapacity.projectedLabel (source h R E a m p) 0 B j
      (NativeLocalParentCells.cellLabel D a (2^m) p
        (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p) i) k) := by
  rw [NativeCoarseShadingCapacity.projectedLabel,hmesh,zero_front_formula,source_line]
  have hm : mesh (source h R E a m p)=localMesh D (2^m) := by
    rw [mesh,source_thickness,localMesh]
    ring
  rw [hm]
  rfl

lemma globalLabel_eq_projected {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (K B : ℕ) (hmesh : (B:ℝ)*D.thickness/128=32/(K:ℝ)) (i : Fin n) (k : Index) :
    globalLabel D a K i k=NativeCoarseShadingCapacity.projectedLabel D a B i k := by
  rw [NativeCoarseShadingCapacity.projectedLabel,hmesh]
  rfl

/-- The actual dyadic scale matching includes the six-level shift:
global f=m+ell-6, local relative ell, with 6≤ell and f≤level. -/
theorem dyadic_double_label_mem_menu {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m ell : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hell : 6 ≤ ell)
    (hfl : m+ell-6 ≤ level) (p : Parent) (i jg jr : Fin n) (k : Index)
    (hk : k∈original i) (hip : parentLabel D a (2^m) i=p)
    (hg : parentLabel D a (2^(m+ell-6)) jg=parentLabel D a (2^(m+ell-6)) i)
    (hr : relativeLabel D a (2^m) p (2^ell) jr=relativeLabel D a (2^m) p (2^ell) i) :
    doubleLabel D a (2^m) (2^ell) p jr i k ∈
      pointMenu (2^m) (2^(m+ell-6)) (2^ell) p (globalLabel D a (2^(m+ell-6)) jg k) := by
  have hm : m ≤ level := by omega
  have hKM : ((2^(m+ell-6):ℕ):ℝ)*64=((2^m:ℕ):ℝ)*((2^ell:ℕ):ℝ) := by
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    calc
      _ = (2:ℝ)^(m+ell-6)*(2:ℝ)^6 := by norm_num
      _ = (2:ℝ)^(m+ell) := by rw [←pow_add]; congr 1; omega
      _ = _ := by rw [pow_add]
  have hNscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 := by
    rw [NativeLocalParentScales.relative_scale hdy hm]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hKscale : ((2^(m+ell-6):ℕ):ℝ)*D.thickness ≤ 1 := by
    rw [NativeLocalParentScales.relative_scale hdy hfl]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  exact double_label_mem_menu h original horiginal ha (2^m) (2^(m+ell-6)) (2^ell)
    (by positivity) (by positivity) (by positivity) hKM hNscale hKscale p i jg jr k hk hip hg hr

/-- Forward point-menu cardinality on one literal original E. The two
representative maps are fixed inputs; the bound does not select or prune E. -/
theorem dyadic_point_fiber_image_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m ell : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hell : 6 ≤ ell)
    (hfl : m+ell-6 ≤ level) (p : Parent)
    (globalRep relativeRep : (Fin n × Index) → Fin n)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hp : ∀z∈E,parentLabel D a (2^m) z.1=p)
    (hg : ∀z∈E,parentLabel D a (2^(m+ell-6)) (globalRep z)=parentLabel D a (2^(m+ell-6)) z.1)
    (hr : ∀z∈E,relativeLabel D a (2^m) p (2^ell) (relativeRep z)=relativeLabel D a (2^m) p (2^ell) z.1)
    (q : Index) :
    ((E.filter (fun z => globalLabel D a (2^(m+ell-6)) (globalRep z) z.2=q)).image
      (fun z => doubleLabel D a (2^m) (2^ell) p (relativeRep z) z.1 z.2)).card ≤ 81 := by
  rw [←pointMenu_card (2^m) (2^(m+ell-6)) (2^ell) p q]
  apply card_le_card
  intro w hw
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
  obtain ⟨hz,hzq⟩ := mem_filter.mp hz
  have hh := dyadic_double_label_mem_menu h original horiginal ha level m ell hdy hell hfl
    p z.1 (globalRep z) (relativeRep z) z.2 ((mem_incidences original z.1 z.2).mp (hE hz))
    (hp z hz) (hg z hz) (hr z hz)
  rwa [hzq] at hh

end NativeRelativeCoarsePointMenu
