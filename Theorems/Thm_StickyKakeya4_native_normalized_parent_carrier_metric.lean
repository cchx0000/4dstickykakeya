import Theorems.Thm_StickyKakeya4_native_unit_parent_normalization
import Theorems.Thm_StickyKakeya4_native_contracted_unit_parent
import Theorems.Thm_StickyKakeya4_native_unit_parent_directions
import Theorems.Thm_StickyKakeya4_native_unit_parent_dyadic
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeNormalizedParentCarrierMetric
open Classical StickyKakeya4 NativeOriginalCellChartGeometry NativeOriginalParentSelection
open NativeUnitParentNormalization NativeContractedUnitParent
open scoped RealInnerProductSpace

lemma euclidean_three_norm_le_two (x : E3) (r : ℝ) (hr : 0≤r)
    (hx : ∀ j, |x j|≤r) : ‖x‖≤2*r := by
  have hs : ‖x‖^2≤3*r^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three]
    have h0 := pow_le_pow_left₀ (abs_nonneg _) (hx 0) 2
    have h1 := pow_le_pow_left₀ (abs_nonneg _) (hx 1) 2
    have h2 := pow_le_pow_left₀ (abs_nonneg _) (hx 2) 2
    simp only [sq_abs] at h0 h1 h2
    nlinarith only [h0,h1,h2]
  nlinarith only [hs,norm_nonneg x,sq_nonneg r,hr]

lemma heightPoint_zero_norm (b : E3) : ‖ActualSlopeSource.heightPoint b 0‖=‖b‖ := by
  have hs : ‖ActualSlopeSource.heightPoint b 0‖^2=‖b‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_castSucc]
    simp only [ActualSlopeSource.heightPoint_castSucc,ActualSlopeSource.heightPoint_last,
      zero_pow (by decide : 2≠0),add_zero]
  nlinarith only [hs,norm_nonneg (ActualSlopeSource.heightPoint b 0),norm_nonneg b]

lemma heightPoint_zero_sub_norm (b c : E3) :
    ‖ActualSlopeSource.heightPoint b 0-ActualSlopeSource.heightPoint c 0‖=‖b-c‖ := by
  have he : ActualSlopeSource.heightPoint b 0-ActualSlopeSource.heightPoint c 0=
      ActualSlopeSource.heightPoint (b-c) 0 := by
    ext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [PiLp.sub_apply,ActualSlopeSource.heightPoint_last,sub_self]
    · simp only [PiLp.sub_apply,ActualSlopeSource.heightPoint_castSucc]
  rw [he,heightPoint_zero_norm]

/-- The actual normalized graph direction is two-Lipschitz in the genuine
Euclidean slope vector, with no source or compactness premise. -/
theorem graph_direction_dist_le (a b a' b' : E3) :
    dist (direction (NativeGraphMarkedLine.ofGraph a b 0))
      (direction (NativeGraphMarkedLine.ofGraph a' b' 0))≤2*‖a-a'‖ := by
  rw [dist_eq_norm]
  change ‖NormedSpace.normalize (northSlopeLift a)-NormedSpace.normalize (northSlopeLift a')‖≤_
  have hh := norm_normalize_sub_normalize_le_two_of_one_le (northSlopeLift a) (northSlopeLift a')
    (northSlopeLift_norm_ge_one a) (northSlopeLift_norm_ge_one a')
  simpa only [northSlopeLift_sub_norm] using hh

/-- Orthogonal carrier offsets are Lipschitz in an actual graph center and
its genuine unit direction. This is an explicit coordinate calculation. -/
theorem orthogonal_offset_dist_le (x y u v : E4) (hu : ‖u‖=1) (hv : ‖v‖=1) :
    ‖(x-inner ℝ x u • u)-(y-inner ℝ y v • v)‖≤
      2*‖x-y‖+2*‖y‖*‖u-v‖ := by
  have hm : |inner ℝ x u-inner ℝ y v|≤‖x-y‖+‖y‖*‖u-v‖ := by
    have he : inner ℝ x u-inner ℝ y v=inner ℝ (x-y) u+inner ℝ y (u-v) := by
      rw [inner_sub_left,inner_sub_right]
      ring
    rw [he]
    have h₁ := abs_real_inner_le_norm (x-y) u
    have h₂ := abs_real_inner_le_norm y (u-v)
    rw [hu,mul_one] at h₁
    exact (abs_add_le _ _).trans (add_le_add h₁ h₂)
  have hm' : |inner ℝ y v|≤‖y‖ := by
    simpa only [hv,mul_one] using abs_real_inner_le_norm y v
  have hp : ‖inner ℝ x u • u-inner ℝ y v • v‖≤‖x-y‖+2*‖y‖*‖u-v‖ := by
    have he : inner ℝ x u • u-inner ℝ y v • v=
        (inner ℝ x u-inner ℝ y v) • u+inner ℝ y v • (u-v) := by module
    rw [he]
    have ht := norm_add_le ((inner ℝ x u-inner ℝ y v) • u) (inner ℝ y v • (u-v))
    simp only [norm_smul,Real.norm_eq_abs,hu,mul_one] at ht
    have hh := mul_le_mul_of_nonneg_right hm' (norm_nonneg (u-v))
    linarith only [ht,hm,hh]
  have he : (x-inner ℝ x u • u)-(y-inner ℝ y v • v)=
      (x-y)-(inner ℝ x u • u-inner ℝ y v • v) := by module
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith only [hp])

/-- On the actual bounded graph chart, slope errors r and original shifted
intercept errors r give a fixed sixteen-r carrier ball after padding. -/
theorem graph_carrier_dist_le_sixteen (a b a' b' : E3) (r : ℝ) (hr : 0≤r)
    (ha : ‖a-a'‖≤2*r) (hb : ‖b-b'‖≤r/2) (hb' : ‖b'‖≤1) :
    dist (direction (NativeGraphMarkedLine.ofGraph a b 0),offset (NativeGraphMarkedLine.ofGraph a b 0))
      (direction (NativeGraphMarkedLine.ofGraph a' b' 0),offset (NativeGraphMarkedLine.ofGraph a' b' 0))≤16*r := by
  let u : E4 := northSlopeDirection a
  let v : E4 := northSlopeDirection a'
  let x := ActualSlopeSource.heightPoint b 0
  let y := ActualSlopeSource.heightPoint b' 0
  have hu : ‖u‖=1 := (northSlopeDirection a).property
  have hv : ‖v‖=1 := (northSlopeDirection a').property
  have hdir : ‖u-v‖≤4*r := by
    have hh := graph_direction_dist_le a b a' b'
    change ‖u-v‖≤2*‖a-a'‖ at hh
    linarith only [hh,ha]
  have hxy : ‖x-y‖≤r/2 := by simpa only [x,y,heightPoint_zero_sub_norm] using hb
  have hy : ‖y‖≤1 := by simpa only [y,heightPoint_zero_norm] using hb'
  have ho := orthogonal_offset_dist_le x y u v hu hv
  have hprod := mul_le_mul hy hdir (norm_nonneg (u-v)) (by norm_num : (0:ℝ)≤1)
  have hoff : ‖(x-inner ℝ x u • u)-(y-inner ℝ y v • v)‖≤16*r := by
    nlinarith only [ho,hprod,hxy,hr]
  simp only [NativeGraphMarkedLine.ofGraph,zero_smul,add_zero,direction,offset]
  change max (dist u v)
    (dist (x-inner ℝ x u • u) (y-inner ℝ y v • v))≤16*r
  rw [dist_eq_norm,dist_eq_norm]
  exact max_le (by linarith only [hdir,hr]) hoff

lemma normalized_intercept_norm_le_one {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (p : Parent) (i : Fin n) (hi : parentLabel D a 1 i=p) :
    ‖newIntercept (D.line i) (mesh D) (shift D a) p‖≤1 := by
  have hb (j : Fin 3) : |newIntercept (D.line i) (mesh D) (shift D a) p j|≤1/4 := by
    have hh := (parameter_box D a p i hi).2 j
    exact abs_le.mpr ⟨by linarith only [hh.1],hh.2.le⟩
  have hh := euclidean_three_norm_le_two _ (1/4) (by norm_num) hb
  linarith only [hh]

/-- The existing extra contraction preserves directions and is nonexpanding
on the literal direction/orthogonal-offset carrier metric. -/
theorem contractLine_carrier_dist_le (l l' : MarkedLine) :
    dist (direction (contractLine l),offset (contractLine l))
      (direction (contractLine l'),offset (contractLine l'))≤
        dist (direction l,offset l) (direction l',offset l') := by
  change max (dist (direction l) (direction l'))
      (dist ((1/32:ℝ) • offset l) ((1/32:ℝ) • offset l'))≤
    max (dist (direction l) (direction l')) (dist (offset l) (offset l'))
  apply max_le_max le_rfl
  rw [dist_smul₀]
  norm_num
  linarith only [dist_nonneg (x:=offset l) (y:=offset l')]

/-- Literal original slope/shifted-intercept coordinate control passes
through the selected /16 padded parent and final /32 carrier contraction. -/
theorem normalized_parent_carrier_dist_le {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (p : Parent) (i j : Fin n) (r : ℝ) (hr : 0≤r)
    (_hi : parentLabel D a 1 i=p) (hj : parentLabel D a 1 j=p)
    (hs : ∀ k, |slope (D.line i) k-slope (D.line j) k|≤r)
    (hb : ∀ k, |shiftedIntercept (D.line i) (mesh D) (shift D a) k-
      shiftedIntercept (D.line j) (mesh D) (shift D a) k|≤r) :
    dist (direction (NativeContractedUnitParent.line D a p i),offset (NativeContractedUnitParent.line D a p i))
      (direction (NativeContractedUnitParent.line D a p j),offset (NativeContractedUnitParent.line D a p j))≤16*r := by
  have hsu : ‖newSlope (D.line i) p-newSlope (D.line j) p‖≤2*r := by
    apply euclidean_three_norm_le_two _ r hr
    intro k
    simpa only [newSlope,PiLp.sub_apply,sub_sub_sub_cancel_right] using hs k
  have hbi : ‖newIntercept (D.line i) (mesh D) (shift D a) p-
      newIntercept (D.line j) (mesh D) (shift D a) p‖≤r/2 := by
    have hh := euclidean_three_norm_le_two
      (newIntercept (D.line i) (mesh D) (shift D a) p-newIntercept (D.line j) (mesh D) (shift D a) p)
      (r/4) (by positivity) (by
        intro k
        change |(shiftedIntercept (D.line i) (mesh D) (shift D a) k-(p.2 k:ℝ))/4-
          (shiftedIntercept (D.line j) (mesh D) (shift D a) k-(p.2 k:ℝ))/4|≤r/4
        rw [←sub_div,sub_sub_sub_cancel_right,abs_div]
        norm_num
        linarith only [hb k])
    linarith only [hh]
  have hpad := graph_carrier_dist_le_sixteen (newSlope (D.line i) p)
    (newIntercept (D.line i) (mesh D) (shift D a) p) (newSlope (D.line j) p)
    (newIntercept (D.line j) (mesh D) (shift D a) p) r hr hsu hbi
    (normalized_intercept_norm_le_one D a p j hj)
  exact (contractLine_carrier_dist_le (newLine (D.line i) (mesh D) (shift D a) p)
    (newLine (D.line j) (mesh D) (shift D a) p)).trans hpad

lemma same_floor_mul_close (x y : ℝ) (N : ℕ) (hN : 0<N)
    (hcell : ⌊(N:ℝ)*x⌋=⌊(N:ℝ)*y⌋) : |x-y|≤1/(N:ℝ) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hx₁ := Int.floor_le ((N:ℝ)*x)
  have hx₂ := Int.lt_floor_add_one ((N:ℝ)*x)
  have hy₁ := Int.floor_le ((N:ℝ)*y)
  have hy₂ := Int.lt_floor_add_one ((N:ℝ)*y)
  rw [hcell] at hx₁ hx₂
  have hh : |(N:ℝ)*x-(N:ℝ)*y|≤1 := abs_le.mpr
    ⟨by linarith only [hx₁,hy₂],by linarith only [hx₂,hy₁]⟩
  rw [←mul_sub,abs_mul,abs_of_pos hNp] at hh
  exact (le_div_iff₀ hNp).mpr (by nlinarith only [hh])

/-- Every occupied original parameter cell of side 1/N maps into the
actual final carrier ball of radius 16/N about any of its original labels. -/
theorem same_parent_cell_carrier_dist_le {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (p : Parent) (i j : Fin n) (N : ℕ) (hN : 0<N)
    (hi : parentLabel D a 1 i=p) (hj : parentLabel D a 1 j=p)
    (hcell : parentLabel D a N i=parentLabel D a N j) :
    dist (direction (NativeContractedUnitParent.line D a p i),offset (NativeContractedUnitParent.line D a p i))
      (direction (NativeContractedUnitParent.line D a p j),offset (NativeContractedUnitParent.line D a p j))≤16/(N:ℝ) := by
  have hh := normalized_parent_carrier_dist_le D a p i j (1/(N:ℝ)) (by positivity) hi hj
    (fun k => same_floor_mul_close _ _ N hN (congrFun (congrArg Prod.fst hcell) k))
    (fun k => same_floor_mul_close _ _ N hN (congrFun (congrArg Prod.snd hcell) k))
  simpa only [mul_one_div] using hh

end NativeNormalizedParentCarrierMetric
