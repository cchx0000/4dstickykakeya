import Theorems.Thm_StickyKakeya4_native_coarse_point_multiplicity

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4800000

noncomputable section
namespace NativeSpatialAngularGeometry
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalCellChartGeometry NativeOriginalParentPhysicalData
open NativeOriginalPaddedCells NativeLocalParentPhysicalMap NativeContractedUnitParent
open NativeNormalizedParentCarrierMetric
open scoped BigOperators

/-- A spatial cube of side64/M containing the LITERAL original cell center.
This is not identified with either the microcell or its projected shadow. -/
def spatialLabel {n : ℕ} (D : FiniteScaleSource n) (M : ℕ) (k : Index) : Index :=
  wzDyadicCellIndex (64/(M:ℝ)) (cellCenter (mesh D) k)

/-- Literal slope-grid labels of the original marked lines. -/
def angularLabel {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (i : Fin n) : Fin 3 → ℤ :=
  fun v => ⌊(N:ℝ)*slope (D.line i) v⌋

lemma parent_angular {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (i : Fin n) :
    (parentLabel D a N i).1=angularLabel D N i := rfl

/-- A fixed integer box; all later capacities are computed from this menu. -/
def integerBox (d K : ℕ) (q : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun v => Icc (q v-(K:ℤ)) (q v+K))

lemma integerBox_card (d K : ℕ) (q : Fin d → ℤ) : (integerBox d K q).card=(2*K+1)^d := by
  have hc (v : Fin d) : (Icc (q v-(K:ℤ)) (q v+K)).card=2*K+1 := by
    have hh : ((Icc (q v-(K:ℤ)) (q v+K)).card:ℤ)=2*(K:ℤ)+1 := by
      rw [Int.card_Icc_of_le _ _ (by omega)]
      ring
    exact_mod_cast hh
  simp only [integerBox,Fintype.card_piFinset,hc,prod_const,card_univ,Fintype.card_fin]

lemma floor_mem_interval {x y : ℝ} (K : ℕ) (hxy : |x-y| ≤ K) :
    ⌊x⌋∈Icc (⌊y⌋-((K+1:ℕ):ℤ)) (⌊y⌋+((K+1:ℕ):ℤ)) := by
  have hxlo := Int.floor_le x
  have hxhi := Int.lt_floor_add_one x
  have hylo := Int.floor_le y
  have hyhi := Int.lt_floor_add_one y
  have hb := abs_le.mp hxy
  apply mem_Icc.mpr
  constructor
  · have hh : (⌊y⌋:ℝ)-((K:ℝ)+1) ≤ (⌊x⌋:ℝ) := by linarith
    exact_mod_cast hh
  · have hh : (⌊x⌋:ℝ) ≤ (⌊y⌋:ℝ)+((K:ℝ)+1) := by linarith
    exact_mod_cast hh

lemma same_cell_coordinate_close {width : ℝ} (hw : 0 < width) (x y : E4)
    (he : wzDyadicCellIndex width x=wzDyadicCellIndex width y) (v : Fin 4) :
    |x v-y v| ≤ width := by
  have hv := congrFun he v
  change ⌊x v/width⌋=⌊y v/width⌋ at hv
  have hxlo := (le_div_iff₀ hw).mp (Int.floor_le (x v/width))
  have hxhi := (div_lt_iff₀ hw).mp (Int.lt_floor_add_one (x v/width))
  have hylo := (le_div_iff₀ hw).mp (Int.floor_le (y v/width))
  have hyhi := (div_lt_iff₀ hw).mp (Int.lt_floor_add_one (y v/width))
  rw [hv] at hxlo hxhi
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

lemma spatial_coordinate_close {n : ℕ} (D : FiniteScaleSource n) (M : ℕ) (hM : 0 < M)
    (k l : Index) (hkl : spatialLabel D M k=spatialLabel D M l) (v : Fin 4) :
    |cellCenter (mesh D) k v-cellCenter (mesh D) l v| ≤ 64/(M:ℝ) :=
  same_cell_coordinate_close (by positivity) _ _ hkl v

lemma chart_spatial_sub {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (k l : Index) (v : Fin 3) :
    (ShearBinFibers.oldCenter (mesh D/4) (chartIndex (shift D a) k)).1 v-
      (ShearBinFibers.oldCenter (mesh D/4) (chartIndex (shift D a) l)).1 v=
        (cellCenter (mesh D) k v.castSucc-cellCenter (mesh D) l v.castSucc)/4 := by
  simp only [ShearBinFibers.oldCenter,chartIndex,cellCenter]
  ring

lemma oldTime_sub {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (k l : Index) :
    oldTime D a k-oldTime D a l=
      (cellCenter (mesh D) k (3:Fin 4)-cellCenter (mesh D) l (3:Fin 4))/4 := by
  simp only [oldTime,ShearBinFibers.oldCenter,chartIndex,cellCenter,Int.cast_sub]
  ring

lemma physicalMap_zero_sub {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (x y : E4) (v : Fin 4) :
    physicalMap D a 1 (0,0) x v-physicalMap D a 1 (0,0) y v=(x v-y v)/512 := by
  refine Fin.lastCases ?_ (fun v => ?_) v
  · simp only [NativeLocalParentPhysicalMap.physicalMap,baseMap,contractPoint,PiLp.smul_apply,smul_eq_mul,
      ActualSlopeSource.heightPoint_last,show (Fin.last 3:Fin 4)=3 by rfl]
    ring
  · simp only [NativeLocalParentPhysicalMap.physicalMap,baseMap,contractPoint,PiLp.smul_apply,smul_eq_mul,
      ActualSlopeSource.heightPoint_castSucc,Nat.cast_one,Pi.zero_apply,Int.cast_zero]
    ring

/-- Common spatial location plus a common angular cell confines the actual
shifted intercepts. Both graph residuals come from ORIGINAL shading cells. -/
theorem intercept_close {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) (hscale : (M:ℝ)*D.thickness ≤ 1)
    (i j : Fin n) (k l : Index) (hik : (i,k)∈incidences original) (hjl : (j,l)∈incidences original)
    (hcell : spatialLabel D M k=spatialLabel D M l)
    (hang : angularLabel D N i=angularLabel D N j) (v : Fin 3) :
    |shiftedIntercept (D.line i) (mesh D) (shift D a) v-
      shiftedIntercept (D.line j) (mesh D) (shift D a) v| ≤ 64/(N:ℝ) := by
  have hM : 0 < M := hN.trans_le hNM
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hNMreal : (N:ℝ) ≤ M := by exact_mod_cast hNM
  have hInv : 1/(M:ℝ) ≤ 1/(N:ℝ) := one_div_le_one_div_of_le hNr hNMreal
  have hdN : D.thickness ≤ 1/(N:ℝ) := by
    apply (le_div_iff₀ hNr).mpr
    have hh := (mul_le_mul_of_nonneg_right hNMreal h.1.2.1.le).trans hscale
    simpa only [mul_comm] using hh
  have hi := original_cell_bounds h original horiginal a ha hik
  have hj := original_cell_bounds h original horiginal a ha hjl
  have hs := same_floor_mul_close (slope (D.line i) v) (slope (D.line j) v) N hN
    (congrFun hang v)
  have hvj := slope_bound (D.line j) (h.1.2.2.2.2.1 j) (h.2.1.1 j) v
  have hx : |(ShearBinFibers.oldCenter (mesh D/4) (chartIndex (shift D a) k)).1 v-
      (ShearBinFibers.oldCenter (mesh D/4) (chartIndex (shift D a) l)).1 v| ≤ 16/(M:ℝ) := by
    rw [chart_spatial_sub,abs_div,abs_of_pos (by norm_num : (0:ℝ)<4)]
    have hh := div_le_div_of_nonneg_right (spatial_coordinate_close D M hM k l hcell v.castSucc)
      (by norm_num : (0:ℝ) ≤ 4)
    simpa only [show (64/(M:ℝ))/4=16/(M:ℝ) by ring] using hh
  have ht : |oldTime D a k-oldTime D a l| ≤ 16/(M:ℝ) := by
    rw [oldTime_sub,abs_div,abs_of_pos (by norm_num : (0:ℝ)<4)]
    have hh := div_le_div_of_nonneg_right (spatial_coordinate_close D M hM k l hcell 3)
      (by norm_num : (0:ℝ) ≤ 4)
    simpa only [show (64/(M:ℝ))/4=16/(M:ℝ) by ring] using hh
  have ht0 : |oldTime D a k| ≤ 1 := hi.1
  have hprod1 : |(slope (D.line i) v-slope (D.line j) v)*oldTime D a k| ≤ 1/(N:ℝ) := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul hs ht0 (abs_nonneg _) (by positivity)
  have hprod2 : |slope (D.line j) v*(oldTime D a k-oldTime D a l)| ≤ 32/(M:ℝ) := by
    rw [abs_mul]
    have hh := mul_le_mul hvj ht (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
    simpa only [show (2:ℝ)*(16/(M:ℝ))=32/(M:ℝ) by ring] using hh
  have hp : |slope (D.line i) v*oldTime D a k-slope (D.line j) v*oldTime D a l| ≤
      1/(N:ℝ)+32/(M:ℝ) := by
    calc
      _ = |(slope (D.line i) v-slope (D.line j) v)*oldTime D a k+
        slope (D.line j) v*(oldTime D a k-oldTime D a l)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hprod1 hprod2)
  have heI := hi.2 v
  have heJ := hj.2 v
  change |_ - _ - slope (D.line i) v*oldTime D a k| ≤ _ at heI
  change |_ - _ - slope (D.line j) v*oldTime D a l| ≤ _ at heJ
  have hres : 12*(mesh D/4)=3*D.thickness/2 := by unfold mesh; ring
  rw [hres] at heI heJ
  have hxB := abs_le.mp hx
  have hpB := abs_le.mp hp
  have hiB := abs_le.mp heI
  have hjB := abs_le.mp heJ
  have hNI : (0:ℝ) < (N:ℝ)⁻¹ := inv_pos.mpr hNr
  simp only [div_eq_mul_inv] at hxB hpB hiB hjB hdN hInv ⊢
  apply abs_le.mpr
  constructor <;> linarith only [hxB.1,hxB.2,hpB.1,hpB.2,hiB.1,hiB.2,hjB.1,hjB.2,hdN,hInv,hNI]

/-- At most131^3 actual original phase parents can occur in one finer
spatial cube and one original angular N-cell. -/
theorem phase_parent_image_card {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) (hscale : (M:ℝ)*D.thickness ≤ 1)
    (F : Finset (Fin n × Index)) (hF : F⊆incidences original)
    (q : Index) (u : Fin 3 → ℤ)
    (hspace : ∀z∈F,spatialLabel D M z.2=q)
    (hang : ∀z∈F,angularLabel D N z.1=u) :
    (F.image (fun z => parentLabel D a N z.1)).card ≤ 131^3 := by
  by_cases hne : F.Nonempty
  · obtain ⟨z0,hz0⟩ := hne
    let V := integerBox 3 65 (parentLabel D a N z0.1).2
    have hsub : F.image (fun z => parentLabel D a N z.1) ⊆ V.image (fun v => (u,v)) := by
      intro p hp
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hp
      refine mem_image.mpr ⟨(parentLabel D a N z.1).2,?_,?_⟩
      · apply Fintype.mem_piFinset.mpr
        intro v
        have hh := intercept_close h original horiginal ha N M hN hNM hscale z.1 z0.1 z.2 z0.2
          (hF hz) (hF hz0) ((hspace z hz).trans (hspace z0 hz0).symm)
          ((hang z hz).trans (hang z0 hz0).symm) v
        have hNr : (0:ℝ) < N := by exact_mod_cast hN
        have hhN : |(N:ℝ)*shiftedIntercept (D.line z.1) (mesh D) (shift D a) v-
            (N:ℝ)*shiftedIntercept (D.line z0.1) (mesh D) (shift D a) v| ≤ 64 := by
          rw [←mul_sub,abs_mul,abs_of_pos hNr]
          have ht := mul_le_mul_of_nonneg_left hh hNr.le
          have he : (N:ℝ)*(64/(N:ℝ))=64 := by field_simp
          rwa [he] at ht
        exact floor_mem_interval 64 hhN
      · exact Prod.ext (hang z hz).symm rfl
    calc
      _ ≤ (V.image (fun v => (u,v))).card := card_le_card hsub
      _ ≤ V.card := card_image_le
      _ = _ := integerBox_card 3 65 _
  · rw [not_nonempty_iff_eq_empty.mp hne]
    simp

end NativeSpatialAngularGeometry
