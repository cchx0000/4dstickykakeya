import Theorems.Thm_StickyKakeya4_native_original_parent_selection
import Theorems.Thm_StickyKakeya4_native_graph_marked_line
import Theorems.Thm_StickyKakeya4_euclidean_alignment_patches
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeUnitParentNormalization
open Classical StickyKakeya4 NativeOriginalCellChartGeometry NativeOriginalParentSelection
open scoped RealInnerProductSpace

private lemma heightPoint_fourth (x : E3) (s : ℝ) :
    ActualSlopeSource.heightPoint x s (3:Fin 4)=s := ActualSlopeSource.heightPoint_last x s

/-- The actual affine contraction, height translation, and integer parent shear. -/
def pointMap (s : ℝ) (p : Parent) (x : E4) : E4 :=
  ActualSlopeSource.heightPoint
    (WithLp.toLp 2 (fun j : Fin 3 =>
      (x j.castSucc - (p.1 j : ℝ)*(x (3:Fin 4)-s) - 4*(p.2 j : ℝ))/16))
    ((x (3:Fin 4)-s)/16)

def pointInv (s : ℝ) (p : Parent) (y : E4) : E4 :=
  ActualSlopeSource.heightPoint
    (WithLp.toLp 2 (fun j : Fin 3 =>
      16*y j.castSucc + (p.1 j : ℝ)*(16*y (3:Fin 4)) + 4*(p.2 j : ℝ)))
    (16*y (3:Fin 4)+s)

def newSlope (line : MarkedLine) (p : Parent) : E3 :=
  WithLp.toLp 2 (fun j => slope line j-(p.1 j : ℝ))
def newIntercept (line : MarkedLine) (mesh : ℝ) (shift : ℤ) (p : Parent) : E3 :=
  WithLp.toLp 2 (fun j => (shiftedIntercept line mesh shift j-(p.2 j : ℝ))/4)
def newLine (line : MarkedLine) (mesh : ℝ) (shift : ℤ) (p : Parent) : MarkedLine :=
  NativeGraphMarkedLine.ofGraph (newSlope line p) (newIntercept line mesh shift p) 0

lemma pointInv_pointMap (s : ℝ) (p : Parent) (x : E4) :
    pointInv s p (pointMap s p x)=x := by
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [pointInv,pointMap,heightPoint_fourth,
      show (Fin.last 3:Fin 4)=3 by rfl]
    ring
  · simp only [pointInv,pointMap,ActualSlopeSource.heightPoint_castSucc,
      heightPoint_fourth]
    ring

lemma pointMap_pointInv (s : ℝ) (p : Parent) (x : E4) :
    pointMap s p (pointInv s p x)=x := by
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [pointInv,pointMap,heightPoint_fourth,
      show (Fin.last 3:Fin 4)=3 by rfl]
    ring
  · simp only [pointInv,pointMap,ActualSlopeSource.heightPoint_castSucc,
      heightPoint_fourth]
    ring

/-- The new parameters are literal fractional parts of the selected original
unit parent; the intercept is contracted by the fixed dyadic factor four. -/
theorem parameter_box {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (p : Parent)
    (i : Fin n) (hp : parentLabel D a 1 i=p) :
    (∀ j, newSlope (D.line i) p j ∈ Set.Ico (0:ℝ) 1) ∧
      (∀ j, newIntercept (D.line i) (mesh D) (shift D a) p j ∈ Set.Ico (0:ℝ) (1/4)) := by
  have hp1 (j : Fin 3) : ⌊slope (D.line i) j⌋=p.1 j := by
    simpa only [parentLabel,Nat.cast_one,one_mul] using congrFun (congrArg Prod.fst hp) j
  have hp2 (j : Fin 3) : ⌊shiftedIntercept (D.line i) (mesh D) (shift D a) j⌋=p.2 j := by
    simpa only [parentLabel,Nat.cast_one,one_mul] using congrFun (congrArg Prod.snd hp) j
  constructor
  · intro j
    have hlo := Int.floor_le (slope (D.line i) j)
    have hhi := Int.lt_floor_add_one (slope (D.line i) j)
    rw [hp1 j] at hlo hhi
    change 0 ≤ slope (D.line i) j-(p.1 j:ℝ) ∧ slope (D.line i) j-(p.1 j:ℝ)<1
    constructor <;> linarith
  · intro j
    have hlo := Int.floor_le (shiftedIntercept (D.line i) (mesh D) (shift D a) j)
    have hhi := Int.lt_floor_add_one (shiftedIntercept (D.line i) (mesh D) (shift D a) j)
    rw [hp2 j] at hlo hhi
    change 0 ≤ (shiftedIntercept (D.line i) (mesh D) (shift D a) j-(p.2 j:ℝ))/4 ∧
      (shiftedIntercept (D.line i) (mesh D) (shift D a) j-(p.2 j:ℝ))/4<1/4
    constructor <;> linarith

lemma map_rawFront_graph (line : MarkedLine) (m : ℝ) (k : ℤ) (p : Parent) (t : ℝ)
    (hc : direction line (3:Fin 4) ≠ 0) :
    pointMap ((k:ℝ)*m) p (rawFrontParam (line,t)) =
      ActualSlopeSource.heightPoint
        (newIntercept line m k p +
          ((rawFrontParam (line,t) (3:Fin 4)-(k:ℝ)*m)/16) • newSlope line p)
        ((rawFrontParam (line,t) (3:Fin 4)-(k:ℝ)*m)/16) := by
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [pointMap,ActualSlopeSource.heightPoint_last]
  · simp only [pointMap,ActualSlopeSource.heightPoint_castSucc,
      PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,newIntercept,newSlope,shiftedIntercept]
    rw [raw_graph_identity line t hc j]
    ring

/-- Original common-height segments are contracted strictly inside the
padded unit segment. This uses the actual affine mark, not just its carrier. -/
theorem original_front_maps_into_padded_front {n : ℕ} {D : FiniteScaleSource n}
    {eta a : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀ i, wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (p : Parent) (i : Fin n) (hp : parentLabel D a 1 i=p) :
    pointMap ((shift D a:ℝ)*mesh D) p '' unitFront {D.line i} ⊆
      unitFront {newLine (D.line i) (mesh D) (shift D a) p} := by
  rintro x ⟨q,⟨line,hline,t,ht,rfl⟩,rfl⟩
  have he : line=D.line i := by simpa using hline
  subst line
  have hc : 0 < direction (D.line i) (3:Fin 4) := by linarith [h.2.1.1 i]
  change pointMap ((shift D a:ℝ)*mesh D) p (rawFrontParam (D.line i,t)) ∈
    unitFront {newLine (D.line i) (mesh D) (shift D a) p}
  rw [map_rawFront_graph _ _ _ _ _ hc.ne']
  apply NativeGraphMarkedLine.graphPoint_mem_unitFront
  · intro j
    have hj := (parameter_box D a p i hp).1 j
    exact abs_le.mpr ⟨by linarith [hj.1],hj.2.le⟩
  · have hm : 0 < mesh D := half_pos h.1.2.1
    have hm1 : mesh D ≤ 1/2 := by dsimp [mesh]; linarith [h.1.2.2.1]
    have hlo : (shift D a:ℝ)*mesh D ≤ a :=
      (le_div_iff₀ hm).mp (Int.floor_le (a/mesh D))
    have hhi : a < ((shift D a:ℝ)+1)*mesh D :=
      (div_lt_iff₀ hm).mp (Int.lt_floor_add_one (a/mesh D))
    have hh := raw_height_from_common (D.line i) (h.1.2.2.2.2.1 i) hc.ne' (ha i) ht
    obtain ⟨hl,hu⟩ := abs_le.mp hh
    rw [sub_zero]
    apply abs_le.mpr
    constructor <;> nlinarith

/-- The padded original image has a fixed genuine common slab centered at zero. -/
theorem padded_line_common_slab {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (p : Parent) (i : Fin n) (hp : parentLabel D a 1 i=p) :
    IsValidLine (newLine (D.line i) (mesh D) (shift D a) p) ∧
      (1/2:ℝ) ≤ direction (newLine (D.line i) (mesh D) (shift D a) p) (3:Fin 4) ∧
      ContainsWZHeightSlab (newLine (D.line i) (mesh D) (shift D a) p)
        (Set.Icc (-(1/4:ℝ)) (1/4:ℝ)) := by
  have hb (j : Fin 3) : |newSlope (D.line i) p j| ≤ 1 := by
    have hj := (parameter_box D a p i hp).1 j
    exact abs_le.mpr ⟨by linarith [hj.1],hj.2.le⟩
  refine ⟨NativeGraphMarkedLine.valid _ _ _,NativeGraphMarkedLine.direction_fourth_ge_half _ _ _ hb,?_⟩
  simpa only [newLine,zero_sub,zero_add] using NativeGraphMarkedLine.contains_height_slab
    (newSlope (D.line i) p) (newIntercept (D.line i) (mesh D) (shift D a) p) 0 hb

lemma parent_slope_bound {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (p : Parent) (i : Fin n)
    (hp : parentLabel D a 1 i=p) (j : Fin 3) : |(p.1 j:ℝ)| ≤ 2 := by
  have hs := slope_bound (D.line i) (h.1.2.2.2.2.1 i) (h.2.1.1 i) j
  have he : ⌊slope (D.line i) j⌋=p.1 j := by
    simpa only [parentLabel,Nat.cast_one,one_mul] using congrFun (congrArg Prod.fst hp) j
  have hlo : (-2:ℤ) ≤ p.1 j := by
    rw [←he]
    simpa only [show ⌊(-2:ℝ)⌋ = (-2:ℤ) by norm_num] using Int.floor_mono (abs_le.mp hs).1
  have hhi : p.1 j ≤ (2:ℤ) := by
    rw [←he]
    simpa using Int.floor_mono (abs_le.mp hs).2
  exact abs_le.mpr ⟨by exact_mod_cast hlo,by exact_mod_cast hhi⟩

/-- Uniform physical contraction, including the bounded integer parent shear. -/
theorem pointMap_dist_le (s : ℝ) (p : Parent) (hp : ∀ j, |(p.1 j:ℝ)| ≤ 2)
    (x y : E4) : dist (pointMap s p x) (pointMap s p y) ≤ dist x y/2 := by
  have hc (j : Fin 4) : |x j-y j| ≤ dist x y := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le x y j
  have hh (j : Fin 3) :
      |pointMap s p x j.castSucc-pointMap s p y j.castSucc| ≤ 3*dist x y/16 := by
    have he : pointMap s p x j.castSucc-pointMap s p y j.castSucc =
        ((x j.castSucc-y j.castSucc)-(p.1 j:ℝ)*(x (3:Fin 4)-y (3:Fin 4)))/16 := by
      simp only [pointMap,ActualSlopeSource.heightPoint_castSucc]
      ring
    rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<16)]
    apply (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ)<16)).mpr
    have hm : |(p.1 j:ℝ)*(x (3:Fin 4)-y (3:Fin 4))| ≤ 2*dist x y := by
      rw [abs_mul]
      exact mul_le_mul (hp j) (hc 3) (abs_nonneg _) (by norm_num)
    have hb := (abs_sub (x j.castSucc-y j.castSucc) ((p.1 j:ℝ)*(x (3:Fin 4)-y (3:Fin 4)))).trans
      (add_le_add (hc j.castSucc) hm)
    linarith
  have ht : |pointMap s p x (3:Fin 4)-pointMap s p y (3:Fin 4)| ≤ dist x y/16 := by
    have he : pointMap s p x (3:Fin 4)-pointMap s p y (3:Fin 4) =
        (x (3:Fin 4)-y (3:Fin 4))/16 := by
      simp only [pointMap,heightPoint_fourth]
      ring
    rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<16)]
    exact div_le_div_of_nonneg_right (hc 3) (by norm_num)
  have hs : dist (pointMap s p x) (pointMap s p y)^2 ≤
      3*(3*dist x y/16)^2+(dist x y/16)^2 := by
    rw [EuclideanSpace.dist_sq_eq,Fin.sum_univ_castSucc,Fin.sum_univ_three]
    have h0 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 3*dist x y/16)).mpr (hh 0)
    have h1 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 3*dist x y/16)).mpr (hh 1)
    have h2 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 3*dist x y/16)).mpr (hh 2)
    have h3 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ dist x y/16)).mpr ht
    simp only [sq_abs] at h0 h1 h2 h3
    simp only [Real.dist_eq,sq_abs,show (Fin.last 3:Fin 4)=3 by rfl]
    nlinarith
  nlinarith [dist_nonneg (x:=x) (y:=y),dist_nonneg (x:=pointMap s p x) (y:=pointMap s p y)]

/-- Every point of each ORIGINAL physical tube maps inside the actual padded
new marked tube at half the original thickness. -/
theorem original_tube_maps_into_padded_tube {n : ℕ} {D : FiniteScaleSource n}
    {eta a : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀ i, wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (p : Parent) (i : Fin n) (hp : parentLabel D a 1 i=p) :
    pointMap ((shift D a:ℝ)*mesh D) p '' markedUnitTube (D.line i) D.thickness ⊆
      markedUnitTube (newLine (D.line i) (mesh D) (shift D a) p) (D.thickness/2) := by
  rintro y ⟨x,hx,rfl⟩
  change Metric.infDist _ _ ≤ D.thickness/2
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨t,ht,hxt⟩ := exists_rawFrontParam_dist_lt_of_infDist_le
    (D.line i) x hx (show 0<2*eps by positivity)
  have hfront := original_front_maps_into_padded_front h ha p i hp
    (Set.mem_image_of_mem _ (rawFrontParam_mem_unitFront_singleton (D.line i) ht))
  have hc := pointMap_dist_le ((shift D a:ℝ)*mesh D) p (parent_slope_bound h p i hp)
    x (rawFrontParam (D.line i,t))
  exact (Metric.infDist_le_dist_of_mem hfront).trans (hc.trans (by linarith))

/-- A fixed compact marked-line class, chosen before the source and scale. -/
def fixedCompactClass : Set MarkedLine := Metric.closedBall 0 2
lemma fixedCompactClass_compact : IsCompact fixedCompactClass := isCompact_closedBall _ _

theorem padded_line_mem_fixedCompactClass {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (p : Parent) (i : Fin n) (hp : parentLabel D a 1 i=p) :
    newLine (D.line i) (mesh D) (shift D a) p ∈ fixedCompactClass := by
  let u := newSlope (D.line i) p
  let v := newIntercept (D.line i) (mesh D) (shift D a) p
  let theta : E4 := northSlopeDirection u
  let x0 := ActualSlopeSource.heightPoint v 0
  have htheta : ‖theta‖=1 := (northSlopeDirection u).property
  have hv (j : Fin 3) : |v j| ≤ 1/4 := by
    have hh := (parameter_box D a p i hp).2 j
    exact abs_le.mpr ⟨by dsimp [v]; linarith [hh.1],hh.2.le⟩
  have hx : ‖x0‖ ≤ 1 := by
    have hs : ‖x0‖^2 ≤ 3*(1/4:ℝ)^2 := by
      rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_castSucc,Fin.sum_univ_three]
      simp only [x0,ActualSlopeSource.heightPoint_castSucc,ActualSlopeSource.heightPoint_last,zero_pow (by decide : 2≠0),add_zero]
      have h0 := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤1/4)).mpr (hv 0)
      have h1 := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤1/4)).mpr (hv 1)
      have h2 := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤1/4)).mpr (hv 2)
      simp only [sq_abs] at h0 h1 h2
      nlinarith
    nlinarith [norm_nonneg x0]
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
end NativeUnitParentNormalization
