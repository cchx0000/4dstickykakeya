import Theorems.Thm_StickyKakeya4_native_coarse_representative_geometry
import Theorems.Thm_StickyKakeya4_native_padded_source_transport
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeCoarsePhysicalContainment
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalCellChartGeometry NativeOriginalParentSelection
open NativeUnitParentNormalization NativeContractedUnitParent NativeCoarseRepresentativeGeometry
open NativeNormalizedParentCarrierMetric
open scoped RealInnerProductSpace

def graphPoint {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (i : Fin n) (s : ℝ) : E4 :=
  contractPoint (ActualSlopeSource.heightPoint
    (newIntercept (D.line i) (mesh D) (shift D a) (0,0)+s • newSlope (D.line i) (0,0)) s)

lemma graphPoint_mem_front {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (i : Fin n) {s : ℝ} (hs : |s| ≤ 1/4) :
    graphPoint D a i s∈unitFront {NativeContractedUnitParent.line D a (0,0) i} := by
  let l := newLine (D.line i) (mesh D) (shift D a) (0,0)
  have hc : (1/2:ℝ)  ≤  direction l (3:Fin 4) := by
    have hh := h.2.1.1 i
    rwa [←direction_zero_parent h a i] at hh
  have hcp : 0 < direction l (3:Fin 4) := by linarith
  have hu : |(s-0)/direction l (3:Fin 4)| ≤ 1/2 := by
    rw [sub_zero,abs_div,abs_of_pos hcp]
    apply (div_le_iff₀ hcp).mpr
    linarith
  have hf := rawFrontParam_mem_unitFront_singleton l (abs_le.mp hu)
  dsimp only [l,newLine] at hf
  rw [NativeGraphMarkedLine.rawFrontParam_graph] at hf
  exact contract_front l (Set.mem_image_of_mem contractPoint hf)

lemma graphPoint_same_cell_dist {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (hN : 0<N) (i j : Fin n) (hcell : parentLabel D a N i=parentLabel D a N j)
    {s : ℝ} (hs : |s| ≤ 1/4) :
    dist (graphPoint D a i s) (graphPoint D a j s)  ≤  (1/(N:ℝ))/32 := by
  let rho := 1/(N:ℝ)
  have hr : 0 < rho := by dsimp [rho]; positivity
  have hu (k : Fin 3) : |slope (D.line i) k-slope (D.line j) k| ≤ rho :=
    same_floor_mul_close _ _ N hN (congrFun (congrArg Prod.fst hcell) k)
  have hb (k : Fin 3) :
      |shiftedIntercept (D.line i) (mesh D) (shift D a) k-
        shiftedIntercept (D.line j) (mesh D) (shift D a) k| ≤ rho :=
    same_floor_mul_close _ _ N hN (congrFun (congrArg Prod.snd hcell) k)
  have he : graphPoint D a i s-graphPoint D a j s=
      ActualSlopeSource.heightPoint
        ((1/32:ℝ) • (newIntercept (D.line i) (mesh D) (shift D a) (0,0)-
          newIntercept (D.line j) (mesh D) (shift D a) (0,0)+
          s • (newSlope (D.line i) (0,0)-newSlope (D.line j) (0,0)))) 0 := by
    ext k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp only [graphPoint,contractPoint,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
        ActualSlopeSource.heightPoint_last,sub_self]
    · simp only [graphPoint,contractPoint,PiLp.sub_apply,PiLp.smul_apply,PiLp.add_apply,smul_eq_mul,
        ActualSlopeSource.heightPoint_castSucc]
      ring
  rw [dist_eq_norm,he,heightPoint_zero_norm]
  have hcoord (k : Fin 3) :
      |((1/32:ℝ) • (newIntercept (D.line i) (mesh D) (shift D a) (0,0)-
        newIntercept (D.line j) (mesh D) (shift D a) (0,0)+
        s • (newSlope (D.line i) (0,0)-newSlope (D.line j) (0,0)))) k| ≤ rho/64 := by
    simp only [PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,smul_eq_mul,newIntercept,newSlope,
      Pi.zero_apply,Int.cast_zero,sub_zero]
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/32)]
    have h₁ : |shiftedIntercept (D.line i) (mesh D) (shift D a) k/4-
        shiftedIntercept (D.line j) (mesh D) (shift D a) k/4| ≤ rho/4 := by
      rw [←sub_div,abs_div]
      norm_num
      linarith only [hb k]
    have h₂ : |s*(slope (D.line i) k-slope (D.line j) k)| ≤ rho/4 := by
      rw [abs_mul]
      have hh := mul_le_mul hs (hu k) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/4)
      linarith only [hh]
    have hh := (abs_add_le _ _).trans (add_le_add h₁ h₂)
    linarith only [hh]
  have hh := euclidean_three_norm_le_two _ (rho/64) (by positivity) hcoord
  change _  ≤  rho/32
  linarith only [hh]

lemma physicalMap_dist_zero {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (x y : E4) :
    dist (physicalMap D a (0,0) x) (physicalMap D a (0,0) y) ≤ dist x y/64 := by
  rw [physicalMap,physicalMap,contract_dist]
  have hh := pointMap_dist_le ((shift D a:ℝ)*mesh D) (0,0)
    (by intro j; norm_num) x y
  linarith

lemma original_front_height_bound {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (i : Fin n) {t : ℝ} (ht : t∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) :
    |(rawFrontParam (D.line i,t) (3:Fin 4)-(shift D a:ℝ)*mesh D)/16| ≤ 1/4 := by
  have hc : 0 < direction (D.line i) (3:Fin 4) := by linarith [h.2.1.1 i]
  have hm : 0 < mesh D := half_pos h.1.2.1
  have hm1 : mesh D ≤ 1/2 := by dsimp [mesh]; linarith [h.1.2.2.1]
  have hlo : (shift D a:ℝ)*mesh D ≤ a := (le_div_iff₀ hm).mp (Int.floor_le (a/mesh D))
  have hhi : a<((shift D a:ℝ)+1)*mesh D := (div_lt_iff₀ hm).mp (Int.lt_floor_add_one (a/mesh D))
  have hh := raw_height_from_common (D.line i) (h.1.2.2.2.2.1 i) hc.ne' (ha i) ht
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> nlinarith

/-- One COMMON physical map sends every fine tube in an occupied full parent
inside the genuine coarse representative tube. This is the containment
needed to transfer original convex-Wolff through its exact Jacobian. -/
theorem original_tube_in_representative {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (hN : 0<N) (hscale : (N:ℝ)*D.thickness ≤ 1)
    (i j : Fin n) (hcell : parentLabel D a N i=parentLabel D a N j) :
    physicalMap D a (0,0) '' markedUnitTube (D.line i) D.thickness ⊆
      markedUnitTube (NativeContractedUnitParent.line D a (0,0) j) (64/(N:ℝ)) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hdr : D.thickness ≤ 1/(N:ℝ) := (le_div_iff₀ hNr).mpr (by nlinarith only [hscale])
  rintro y ⟨x,hx,rfl⟩
  change Metric.infDist _ _  ≤  64/(N:ℝ)
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨t,ht,hxt⟩ := exists_rawFrontParam_dist_lt_of_infDist_le
    (D.line i) x hx (show 0<64*eps by positivity)
  let s := (rawFrontParam (D.line i,t) (3:Fin 4)-(shift D a:ℝ)*mesh D)/16
  have hs : |s| ≤ 1/4 := original_front_height_bound h ha i ht
  have hp := graphPoint_mem_front h a j hs
  have he : physicalMap D a (0,0) (rawFrontParam (D.line i,t))=graphPoint D a i s := by
    unfold physicalMap graphPoint
    rw [map_rawFront_graph _ _ _ _ _ (show direction (D.line i) (3:Fin 4)≠0 by linarith [h.2.1.1 i])]
  have hd := graphPoint_same_cell_dist D a N hN i j hcell hs
  have hh := physicalMap_dist_zero D a x (rawFrontParam (D.line i,t))
  have ht' := dist_triangle (physicalMap D a (0,0) x)
    (physicalMap D a (0,0) (rawFrontParam (D.line i,t))) (graphPoint D a j s)
  rw [he] at ht' hh
  apply (Metric.infDist_le_dist_of_mem hp).trans
  have hr : 0<1/(N:ℝ) := by positivity
  have he64 : 64/(N:ℝ)=64*(1/(N:ℝ)) := by ring
  rw [he64]
  nlinarith

end NativeCoarsePhysicalContainment
