import Theorems.Thm_StickyKakeya4_native_unit_parent_directions
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000
noncomputable section
namespace NativeContractedUnitParent
open Classical StickyKakeya4 NativeOriginalParentSelection NativeUnitParentNormalization
open NativeUnitParentDirections
open scoped RealInnerProductSpace

/-- Contract the actual marked center and perpendicular offset, retaining the
actual oriented unit direction and padding back to a genuine unit segment. -/
def contractLine (line : MarkedLine) : MarkedLine :=
  ((direction line,(1/32:ℝ) • offset line),mark line/32)
def contractPoint (x : E4) : E4 := (1/32:ℝ) • x

def line {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (p : Parent) (i : Fin n) : MarkedLine :=
  contractLine (newLine (D.line i) (mesh D) (shift D a) p)
def physicalMap {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (p : Parent) (x : E4) : E4 :=
  contractPoint (pointMap ((shift D a:ℝ)*mesh D) p x)

@[simp] lemma direction_contractLine (l : MarkedLine) : direction (contractLine l)=direction l := rfl

lemma contractLine_valid {l : MarkedLine} (h : IsValidLine l) : IsValidLine (contractLine l) := by
  refine ⟨h.1,?_⟩
  change inner ℝ ((1/32:ℝ) • offset l) (direction l)=0
  rw [real_inner_smul_left,h.2,mul_zero]

lemma contractLine_rawFront (l : MarkedLine) (t : ℝ) :
    contractPoint (rawFrontParam (l,t))=rawFrontParam (contractLine l,t/32) := by
  unfold contractPoint rawFrontParam contractLine offset mark direction
  module

lemma contracted_parameter_mem {t : ℝ} (ht : t ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) :
    t/32 ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ) := by constructor <;> linarith [ht.1,ht.2]

lemma contract_front (l : MarkedLine) :
    contractPoint '' unitFront {l} ⊆ unitFront {contractLine l} := by
  rintro x ⟨q,⟨l',hl,t,ht,rfl⟩,rfl⟩
  have he : l'=l := by simpa using hl
  subst l'
  change contractPoint (rawFrontParam (l,t)) ∈ _
  rw [contractLine_rawFront]
  exact rawFrontParam_mem_unitFront_singleton _ (contracted_parameter_mem ht)

lemma contract_dist (x y : E4) : dist (contractPoint x) (contractPoint y)=dist x y/32 := by
  rw [contractPoint,contractPoint,dist_smul₀]
  norm_num
  ring

lemma contract_tube (l : MarkedLine) (r : ℝ) :
    contractPoint '' markedUnitTube l r ⊆ markedUnitTube (contractLine l) (r/32) := by
  rintro y ⟨x,hx,rfl⟩
  change Metric.infDist _ _ ≤ r/32
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨t,ht,hxt⟩ := exists_rawFrontParam_dist_lt_of_infDist_le l x hx (show 0 < 32*eps by positivity)
  have hf := contract_front l (Set.mem_image_of_mem contractPoint (rawFrontParam_mem_unitFront_singleton l ht))
  exact (Metric.infDist_le_dist_of_mem hf).trans (by rw [contract_dist]; linarith)

lemma contractLine_norm_le (l : MarkedLine) : ‖contractLine l‖ ≤ ‖l‖ := by
  change max (max ‖direction l‖ ‖(1/32:ℝ) • offset l‖) |mark l/32| ≤
    max (max ‖direction l‖ ‖offset l‖) |mark l|
  apply max_le_max
  · apply max_le_max le_rfl
    rw [norm_smul,Real.norm_eq_abs]
    norm_num
    nlinarith [norm_nonneg (offset l)]
  · rw [abs_div]
    norm_num
    nlinarith [abs_nonneg (mark l)]

lemma contractLine_center_height (l : MarkedLine) :
    wzMarkedCenterHeight (contractLine l)=wzMarkedCenterHeight l/32 := by
  unfold wzMarkedCenterHeight
  have he := congrFun (congrArg WithLp.ofLp (contractLine_rawFront l 0)) (3:Fin 4)
  simpa only [contractPoint,PiLp.smul_apply,smul_eq_mul,div_eq_mul_inv,one_mul,zero_mul,mul_comm] using he.symm

/-- The second fixed contraction makes the actual padded tube thickness
compatible with the genuine transformed direction separation. -/
theorem original_tube_maps_into_contracted {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (p : Parent) (i : Fin n) (hp : parentLabel D a 1 i=p) :
    physicalMap D a p '' markedUnitTube (D.line i) D.thickness ⊆
      markedUnitTube (line D a p i) (D.thickness/64) := by
  rintro y ⟨x,hx,rfl⟩
  have hf := original_tube_maps_into_padded_tube h ha p i hp (Set.mem_image_of_mem _ hx)
  have ht := contract_tube (newLine (D.line i) (mesh D) (shift D a) p) (D.thickness/2)
    (Set.mem_image_of_mem contractPoint hf)
  simpa only [line,physicalMap,div_div,show (2:ℝ)*32=64 by norm_num] using ht

lemma contracted_direction_separation {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (p : Parent) (i j : Fin n)
    (hi : parentLabel D a 1 i=p) (hj : parentLabel D a 1 j=p) (hne : i ≠ j) :
    D.thickness/64 ≤ dist (direction (line D a p i)) (direction (line D a p j)) := by
  have hh := normalized_direction_separation h p i j hi hj hne
  change D.thickness/64 ≤ dist (direction (newLine (D.line i) (mesh D) (shift D a) p))
    (direction (newLine (D.line j) (mesh D) (shift D a) p))
  linarith [h.1.2.1]

lemma contracted_line_compact {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (p : Parent)
    (i : Fin n) (hp : parentLabel D a 1 i=p) : line D a p i ∈ fixedCompactClass := by
  have hh := padded_line_mem_fixedCompactClass D a p i hp
  change dist _ 0 ≤ 2 at hh ⊢
  rw [dist_zero_right] at hh ⊢
  exact (contractLine_norm_le _).trans hh

lemma contracted_line_common_slab {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (p : Parent)
    (i : Fin n) (hp : parentLabel D a 1 i=p) :
    IsValidLine (line D a p i) ∧ (1/2:ℝ) ≤ direction (line D a p i) (3:Fin 4) ∧
      ContainsWZHeightSlab (line D a p i) (Set.Icc (-(1/4:ℝ)) (1/4:ℝ)) := by
  obtain ⟨hv,hdir,_hs⟩ := padded_line_common_slab D a p i hp
  have hc : wzMarkedCenterHeight (line D a p i)=0 := by
    rw [line,contractLine_center_height,newLine,NativeGraphMarkedLine.center_height,zero_div]
  refine ⟨contractLine_valid hv,hdir,?_⟩
  have hh := containsWZHeightSlab_of_center_bin (line D a p i)
    (c:=(1/2:ℝ)) (u:=0) (h:=0) (by norm_num) hdir (by rw [hc]) (by rw [hc]; simp)
  simpa only [add_zero,zero_sub,zero_add,show (1/2:ℝ)/2=1/4 by norm_num] using hh
end NativeContractedUnitParent
