import Theorems.Thm_StickyKakeya4_native_coarse_physical_containment
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section
namespace NativeLocalParentGeometry
open Classical StickyKakeya4 NativeOriginalCellChartGeometry NativeOriginalParentSelection
open NativeUnitParentNormalization NativeContractedUnitParent NativeOriginalSlopeCubePacking
open NativeUnitParentDirections
open scoped RealInnerProductSpace

/-- Actual fractional graph coordinates of the chosen ORIGINAL N-parent. -/
def localSlope {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (p : Parent) (i : Fin n) : E3 :=
  WithLp.toLp 2 (fun j => (N:ℝ)*slope (D.line i) j-(p.1 j:ℝ))
def localIntercept {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (p : Parent) (i : Fin n) : E3 :=
  WithLp.toLp 2 (fun j => ((N:ℝ)*shiftedIntercept (D.line i) (mesh D) (shift D a) j-(p.2 j:ℝ))/4)
def baseLine {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (p : Parent) (i : Fin n) : MarkedLine :=
  NativeGraphMarkedLine.ofGraph (localSlope D N p i) (localIntercept D a N p i) 0
def line {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (p : Parent) (i : Fin n) : MarkedLine :=
  contractLine (baseLine D a N p i)

lemma parameter_box {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (p : Parent)
    (i : Fin n) (hp : parentLabel D a N i=p) :
    (∀j,localSlope D N p i j∈Set.Ico (0:ℝ) 1) ∧
      (∀j,localIntercept D a N p i j∈Set.Ico (0:ℝ) (1/4)) := by
  constructor
  · intro j
    have he : ⌊(N:ℝ)*slope (D.line i) j⌋=p.1 j := congrFun (congrArg Prod.fst hp) j
    have hl := Int.floor_le ((N:ℝ)*slope (D.line i) j)
    have hu := Int.lt_floor_add_one ((N:ℝ)*slope (D.line i) j)
    rw [he] at hl hu
    change 0 ≤ (N:ℝ)*slope (D.line i) j-(p.1 j:ℝ) ∧ (N:ℝ)*slope (D.line i) j-(p.1 j:ℝ)<1
    constructor <;> linarith
  · intro j
    have he : ⌊(N:ℝ)*shiftedIntercept (D.line i) (mesh D) (shift D a) j⌋=p.2 j :=
      congrFun (congrArg Prod.snd hp) j
    have hl := Int.floor_le ((N:ℝ)*shiftedIntercept (D.line i) (mesh D) (shift D a) j)
    have hu := Int.lt_floor_add_one ((N:ℝ)*shiftedIntercept (D.line i) (mesh D) (shift D a) j)
    rw [he] at hl hu
    change 0 ≤ ((N:ℝ)*shiftedIntercept (D.line i) (mesh D) (shift D a) j-(p.2 j:ℝ))/4 ∧
      ((N:ℝ)*shiftedIntercept (D.line i) (mesh D) (shift D a) j-(p.2 j:ℝ))/4<1/4
    constructor <;> linarith

lemma localSlope_bound {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (p : Parent)
    (i : Fin n) (hp : parentLabel D a N i=p) (j : Fin 3) : |localSlope D N p i j| ≤ 1 := by
  have hh := (parameter_box D a N p i hp).1 j
  exact abs_le.mpr ⟨by linarith [hh.1],hh.2.le⟩

lemma base_valid_slab {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (p : Parent)
    (i : Fin n) (hp : parentLabel D a N i=p) :
    IsValidLine (baseLine D a N p i) ∧ (1/2:ℝ) ≤ direction (baseLine D a N p i) (3:Fin 4) ∧
      ContainsWZHeightSlab (baseLine D a N p i) (Set.Icc (-(1/4:ℝ)) (1/4:ℝ)) := by
  have hb := localSlope_bound D a N p i hp
  refine ⟨NativeGraphMarkedLine.valid _ _ _,NativeGraphMarkedLine.direction_fourth_ge_half _ _ _ hb,?_⟩
  simpa only [baseLine,zero_sub,zero_add] using
    NativeGraphMarkedLine.contains_height_slab (localSlope D N p i) (localIntercept D a N p i) 0 hb

lemma valid_slab {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (p : Parent)
    (i : Fin n) (hp : parentLabel D a N i=p) :
    IsValidLine (line D a N p i) ∧ (1/2:ℝ) ≤ direction (line D a N p i) (3:Fin 4) ∧
      ContainsWZHeightSlab (line D a N p i) (Set.Icc (-(1/4:ℝ)) (1/4:ℝ)) := by
  obtain ⟨hv,hdir,_hs⟩ := base_valid_slab D a N p i hp
  have hc : wzMarkedCenterHeight (line D a N p i)=0 := by
    rw [line,contractLine_center_height,baseLine,NativeGraphMarkedLine.center_height,zero_div]
  refine ⟨contractLine_valid hv,hdir,?_⟩
  have hh := containsWZHeightSlab_of_center_bin (line D a N p i)
    (c:=(1/2:ℝ)) (u:=0) (h:=0) (by norm_num) hdir (by rw [hc]) (by rw [hc]; simp)
  simpa only [add_zero,zero_sub,zero_add,show (1/2:ℝ)/2=1/4 by norm_num] using hh

lemma slope_line {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (p : Parent)
    (i : Fin n) (j : Fin 3) : slope (line D a N p i) j=localSlope D N p i j := by
  unfold NativeOriginalCellChartGeometry.slope line
  simp only [direction_contractLine]
  unfold baseLine
  rw [NativeGraphMarkedLine.direction_castSucc,NativeGraphMarkedLine.direction_fourth]
  have hn : ‖northSlopeLift (localSlope D N p i)‖≠0 :=
    (zero_lt_one.trans_le (northSlopeLift_norm_ge_one _)).ne'
  field_simp

/-- Actual normalized directions retain the correct relative fine scale. -/
theorem direction_separation {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (N : ℕ) (hN : 0 < N) (p : Parent)
    (i j : Fin n) (hi : parentLabel D a N i=p) (hj : parentLabel D a N j=p) (hne : i≠j) :
    (N:ℝ)*D.thickness/48 ≤ dist (direction (line D a N p i)) (direction (line D a N p j)) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  obtain ⟨_hvi,hci,_hsi⟩ := valid_slab D a N p i hi
  obtain ⟨hvj,hcj,_hsj⟩ := valid_slab D a N p j hj
  have hs : dist (slope (D.line i)) (slope (D.line j)) ≤
      (6*dist (direction (line D a N p i)) (direction (line D a N p j)))/(N:ℝ) := by
    apply (dist_pi_le_iff (by positivity)).mpr
    intro k
    have hh := slope_sub_le_direction_dist _ _ hvj hci hcj k
    rw [slope_line,slope_line] at hh
    have he : localSlope D N p i k-localSlope D N p j k=
        (N:ℝ)*(slope (D.line i) k-slope (D.line j) k) := by dsimp [localSlope]; ring
    rw [he,abs_mul,abs_of_pos hNr] at hh
    rw [Real.dist_eq,le_div_iff₀ hNr]
    nlinarith
  have hd := direction_dist_le_eight_slope_dist (D.line i) (D.line j)
    (h.1.2.2.2.2.1 i) (h.1.2.2.2.2.1 j) (h.2.1.1 i) (h.2.1.1 j)
  have hsep := h.1.2.2.2.2.2.2.2.2.2.1 i j hne
  have hbound := (le_div_iff₀ hNr).mp hs
  nlinarith

lemma base_mem_fixedCompactClass {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (i : Fin n) (hp : parentLabel D a N i=p) : baseLine D a N p i∈fixedCompactClass := by
  let u := localSlope D N p i
  let v := localIntercept D a N p i
  let theta : E4 := northSlopeDirection u
  let x0 := ActualSlopeSource.heightPoint v 0
  have htheta : ‖theta‖=1 := (northSlopeDirection u).property
  have hv (j : Fin 3) : |v j| ≤ 1/4 := by
    have hh := (parameter_box D a N p i hp).2 j
    exact abs_le.mpr ⟨by dsimp [v]; linarith [hh.1],hh.2.le⟩
  have hvNorm : ‖v‖ ≤ 1/2 := by
    have hh := NativeNormalizedParentCarrierMetric.euclidean_three_norm_le_two v (1/4) (by norm_num) hv
    linarith
  have hx : ‖x0‖ ≤ 1 := by
    simpa only [x0,NativeNormalizedParentCarrierMetric.heightPoint_zero_norm] using
      hvNorm.trans (by norm_num : (1/2:ℝ)≤1)
  have hm : |inner ℝ x0 theta| ≤ 1 := by
    have hh := abs_real_inner_le_norm x0 theta
    rw [htheta,mul_one] at hh
    exact hh.trans hx
  have ho : ‖x0-inner ℝ x0 theta • theta‖ ≤ 2 := by
    have hh := norm_sub_le x0 (inner ℝ x0 theta • theta)
    rw [norm_smul,Real.norm_eq_abs,htheta,mul_one] at hh
    linarith
  change dist (NativeGraphMarkedLine.ofGraph u v 0) 0 ≤ 2
  rw [dist_zero_right]
  simp only [NativeGraphMarkedLine.ofGraph,zero_smul,add_zero,Prod.norm_def,Real.norm_eq_abs]
  change max (max ‖theta‖ ‖x0-inner ℝ x0 theta • theta‖) |inner ℝ x0 theta| ≤ 2
  exact max_le (max_le (by rw [htheta]; norm_num) ho) (hm.trans (by norm_num))

lemma mem_fixedCompactClass {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (i : Fin n) (hp : parentLabel D a N i=p) : line D a N p i∈fixedCompactClass := by
  have hh := base_mem_fixedCompactClass D a N p i hp
  change dist _ 0 ≤ 2 at hh ⊢
  rw [dist_zero_right] at hh ⊢
  exact (contractLine_norm_le _).trans hh
end NativeLocalParentGeometry
