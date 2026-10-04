import Theorems.Thm_StickyKakeya4_native_local_parent_geometry
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000
noncomputable section
namespace NativeLocalParentPhysicalMap
open Classical StickyKakeya4 NativeOriginalCellChartGeometry NativeOriginalParentSelection
open NativeUnitParentNormalization NativeContractedUnitParent NativeLocalParentGeometry

/-- One common anisotropic affine map for the entire original N-parent. -/
def baseMap (N : ℕ) (s : ℝ) (p : Parent) (x : E4) : E4 :=
  ActualSlopeSource.heightPoint
    (WithLp.toLp 2 (fun j : Fin 3 =>
      ((N:ℝ)*x j.castSucc-(p.1 j:ℝ)*(x (3:Fin 4)-s)-4*(p.2 j:ℝ))/16))
    ((x (3:Fin 4)-s)/16)
def physicalMap {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (p : Parent) (x : E4) : E4 :=
  contractPoint (baseMap N ((shift D a:ℝ)*mesh D) p x)

lemma map_rawFront_graph {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (i : Fin n) (t : ℝ) (hc : direction (D.line i) (3:Fin 4)≠0) :
    baseMap N ((shift D a:ℝ)*mesh D) p (rawFrontParam (D.line i,t))=
      ActualSlopeSource.heightPoint
        (localIntercept D a N p i +
          ((rawFrontParam (D.line i,t) (3:Fin 4)-(shift D a:ℝ)*mesh D)/16) • localSlope D N p i)
        ((rawFrontParam (D.line i,t) (3:Fin 4)-(shift D a:ℝ)*mesh D)/16) := by
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [baseMap,ActualSlopeSource.heightPoint_last]
  · simp only [baseMap,ActualSlopeSource.heightPoint_castSucc,PiLp.add_apply,PiLp.smul_apply,
      smul_eq_mul,localIntercept,localSlope,shiftedIntercept]
    rw [raw_graph_identity (D.line i) t hc j]
    ring

lemma parent_slope_bound {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (N : ℕ) (hN : 0 < N) (p : Parent)
    (i : Fin n) (hp : parentLabel D a N i=p) (j : Fin 3) : |(p.1 j:ℝ)| ≤ 3*(N:ℝ) := by
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hs := slope_bound (D.line i) (h.1.2.2.2.2.1 i) (h.2.1.1 i) j
  have he : ⌊(N:ℝ)*slope (D.line i) j⌋=p.1 j := congrFun (congrArg Prod.fst hp) j
  have hl := Int.floor_le ((N:ℝ)*slope (D.line i) j)
  have hu := Int.lt_floor_add_one ((N:ℝ)*slope (D.line i) j)
  rw [he] at hl hu
  have hslo := mul_le_mul_of_nonneg_left (abs_le.mp hs).1 (show (0:ℝ) ≤ N by positivity)
  have hshi := mul_le_mul_of_nonneg_left (abs_le.mp hs).2 (show (0:ℝ) ≤ N by positivity)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma baseMap_dist_le (N : ℕ) (hN : 0 < N) (s : ℝ) (p : Parent)
    (hp : ∀j,|(p.1 j:ℝ)| ≤ 3*(N:ℝ)) (x y : E4) :
    dist (baseMap N s p x) (baseMap N s p y) ≤ (N:ℝ)*dist x y/2 := by
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hc (j : Fin 4) : |x j-y j| ≤ dist x y := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le x y j
  have hh (j : Fin 3) :
      |baseMap N s p x j.castSucc-baseMap N s p y j.castSucc| ≤ 4*(N:ℝ)*dist x y/16 := by
    have he : baseMap N s p x j.castSucc-baseMap N s p y j.castSucc=
        ((N:ℝ)*(x j.castSucc-y j.castSucc)-(p.1 j:ℝ)*(x (3:Fin 4)-y (3:Fin 4)))/16 := by
      simp only [baseMap,ActualSlopeSource.heightPoint_castSucc]
      ring
    rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<16)]
    apply (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ)<16)).mpr
    have hm : |(p.1 j:ℝ)*(x (3:Fin 4)-y (3:Fin 4))| ≤ 3*(N:ℝ)*dist x y := by
      rw [abs_mul]
      exact mul_le_mul (hp j) (hc 3) (abs_nonneg _) (by positivity)
    have hn : |(N:ℝ)*(x j.castSucc-y j.castSucc)| ≤ (N:ℝ)*dist x y := by
      rw [abs_mul,abs_of_nonneg (by positivity : (0:ℝ) ≤ N)]
      exact mul_le_mul_of_nonneg_left (hc j.castSucc) (by positivity)
    have hb := (abs_sub ((N:ℝ)*(x j.castSucc-y j.castSucc))
      ((p.1 j:ℝ)*(x (3:Fin 4)-y (3:Fin 4)))).trans (add_le_add hn hm)
    linarith
  have ht : |baseMap N s p x (3:Fin 4)-baseMap N s p y (3:Fin 4)| ≤ (N:ℝ)*dist x y/16 := by
    have he : baseMap N s p x (3:Fin 4)-baseMap N s p y (3:Fin 4)=
        (x (3:Fin 4)-y (3:Fin 4))/16 := by
      simp only [baseMap,show (3:Fin 4)=Fin.last 3 by rfl,ActualSlopeSource.heightPoint_last]
      ring
    rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<16)]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact (hc 3).trans (by nlinarith [dist_nonneg (x:=x) (y:=y)])
  have hs : dist (baseMap N s p x) (baseMap N s p y)^2 ≤
      3*(4*(N:ℝ)*dist x y/16)^2+((N:ℝ)*dist x y/16)^2 := by
    rw [EuclideanSpace.dist_sq_eq,Fin.sum_univ_castSucc,Fin.sum_univ_three]
    have h0 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 4*(N:ℝ)*dist x y/16)).mpr (hh 0)
    have h1 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 4*(N:ℝ)*dist x y/16)).mpr (hh 1)
    have h2 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 4*(N:ℝ)*dist x y/16)).mpr (hh 2)
    have h3 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ (N:ℝ)*dist x y/16)).mpr ht
    simp only [sq_abs] at h0 h1 h2 h3
    simp only [Real.dist_eq,sq_abs,show (Fin.last 3:Fin 4)=3 by rfl]
    nlinarith
  apply (sq_le_sq₀ (dist_nonneg (x:=baseMap N s p x) (y:=baseMap N s p y)) (by positivity)).mp
  nlinarith [sq_nonneg ((N:ℝ)*dist x y)]

/-- The same original common-height witness maps all genuine original front
points into the actual padded local segments. -/
theorem original_front_maps {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (p : Parent) (i : Fin n) (hp : parentLabel D a N i=p) :
    physicalMap D a N p '' unitFront {D.line i}⊆unitFront {NativeLocalParentGeometry.line D a N p i} := by
  rintro x ⟨q,⟨l,hl,t,ht,rfl⟩,rfl⟩
  have he : l=D.line i := by simpa using hl
  subst l
  change physicalMap D a N p (rawFrontParam (D.line i,t)) ∈ _
  unfold physicalMap
  rw [map_rawFront_graph D a N p i t (show direction (D.line i) (3:Fin 4)≠0 by linarith [h.2.1.1 i])]
  have hf := NativeGraphMarkedLine.graphPoint_mem_unitFront
    (localSlope D N p i) (localIntercept D a N p i) 0
    ((rawFrontParam (D.line i,t) (3:Fin 4)-(shift D a:ℝ)*mesh D)/16)
    (localSlope_bound D a N p i hp) (by simpa only [sub_zero] using
      NativeCoarsePhysicalContainment.original_front_height_bound h ha i ht)
  exact contract_front _ (Set.mem_image_of_mem contractPoint hf)

/-- A common actual physical map sends every original fine tube in this
parent into its own actual local tube at thickness N*delta/64. -/
theorem original_tube_maps {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (i : Fin n) (hp : parentLabel D a N i=p) :
    physicalMap D a N p '' markedUnitTube (D.line i) D.thickness⊆
      markedUnitTube (NativeLocalParentGeometry.line D a N p i) ((N:ℝ)*D.thickness/64) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  rintro y ⟨x,hx,rfl⟩
  change Metric.infDist _ _ ≤ (N:ℝ)*D.thickness/64
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨t,ht,hxt⟩ := exists_rawFrontParam_dist_lt_of_infDist_le
    (D.line i) x hx (show 0 < 64*eps/(N:ℝ) by positivity)
  have hf := original_front_maps h ha N p i hp
    (Set.mem_image_of_mem _ (rawFrontParam_mem_unitFront_singleton (D.line i) ht))
  have hc := baseMap_dist_le N hN ((shift D a:ℝ)*mesh D) p (parent_slope_bound h N hN p i hp)
    x (rawFrontParam (D.line i,t))
  have hh : dist (physicalMap D a N p x) (physicalMap D a N p (rawFrontParam (D.line i,t))) ≤
      (N:ℝ)*dist x (rawFrontParam (D.line i,t))/64 := by
    unfold physicalMap
    rw [contract_dist]
    linarith
  apply (Metric.infDist_le_dist_of_mem hf).trans (hh.trans _)
  have ht' := mul_le_mul_of_nonneg_left hxt.le hNr.le
  have he : (N:ℝ)*(D.thickness+64*eps/(N:ℝ))=(N:ℝ)*D.thickness+64*eps := by field_simp
  rw [he] at ht'
  linarith
end NativeLocalParentPhysicalMap
