import Theorems.Thm_StickyKakeya4_native_raw_point_global_profiles
import Theorems.Thm_StickyKakeya4_native_squared_grain_queries
import Theorems.Thm_StickyKakeya4_native_queried_vertex_weights

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeRawPointRankFourRatio
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeJointUniformCoarseRelations
open NativeRawPointSourceProfiles NativeRawPointGlobalProfiles NativeFullCoarseShadow
open NativeCoarsePointMultiplicity NativeBalancedConfiguration NativeMiddleWindowBalance
open NativeConditionalCoarseInterpolation NativeSquaredGrainQueries
open scoped BigOperators ENNReal

/-- Read the two scheduled full-shadow relations directly from the one
original incidence core. The existing relation menu is not enlarged. -/
theorem core_physical_uniformities {n d g level : ℕ} {D : FiniteScaleSource n}
    {eta zeta a : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (L : ℕ) (schedule : Fin g → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : IsCore D original R a eta zeta (menuSize d g) g L
      (relationMenu h R a schedule Rel) (fun j => 2^(schedule j).val) E) (j : Fin g) :
    HasUniformFibers E (coreRadix original R L) (physicalPair h R a level (schedule j).val) ∧
    HasUniformFibers E (coreRadix original R L) (physicalPoint h R a level (schedule j).val) := by
  have hU := H.2.2.2.1
  constructor
  · intro x hx y hy
    simpa only [relationMenu,Fin.addCases_right,Fin.addCases_left,unit_degree_eq_fiber] using
      hU (Fin.natAdd d (Fin.castAdd (g+g) j)) x y hx hy
  · intro x hx y hy
    simpa only [relationMenu,Fin.addCases_right,Fin.addCases_left,unit_degree_eq_fiber] using
      hU (Fin.natAdd d (Fin.natAdd g (Fin.castAdd g j))) x y hx hy

/-- At an actual scheduled stop, the reference core's installed uniformities
bound every literal retained subset's global shadow multiplicity. -/
theorem retained_scheduled_full_upper {n d g level : ℕ} {D : FiniteScaleSource n}
    {eta zeta a seed : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n))
    (E1 E2 : Finset (Fin n × Index)) (h21 : E2⊆E1)
    (L : ℕ) (schedule : Fin g → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : IsCore D original R a eta zeta (menuSize d g) g L
      (relationMenu h R a schedule Rel) (fun j => 2^(schedule j).val) E1)
    (j : Fin g) (HB : HasBalancedScale h R E1 a level (schedule j).val seed) :
    (NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level (schedule j).val E2)).toReal ≤
      (coreRadix original R L:ℝ)^4*
        (D.thickness^(-seed)*(64/((2^(schedule j).val:ℕ):ℝ))^(-NativeFixedCompactKakeyaExponent.extremalExponent)) := by
  have hR1 : ∀z∈E1,z.1∈R := fun z hz => (mem_filter.mp (H.1 hz)).2
  have hR2 : ∀z∈E2,z.1∈R := fun z hz => hR1 z (h21 hz)
  obtain ⟨hPair,hPoint⟩ := core_physical_uniformities h original R E1 L schedule Rel H j
  have hh := subset_image_multiplicity E1 E2 h21 (physicalPair h R a level (schedule j).val)
    (coreRadix original R L) hPair hPoint
  have hB := HB.2.1
  rw [full_source_multiplicity_real h R a level (schedule j).val E1 hR1] at hB
  rw [full_source_multiplicity_real h R a level (schedule j).val E2 hR2]
  exact hh.trans (mul_le_mul_of_nonneg_left hB (by positivity))

/-- Exact scalar cancellation for two physical scales rho and rho squared.
The profile inequalities are used only by the source-facing consumer below. -/
lemma squared_profile_cross {delta rho eta zeta seed t kappa lambda A B coarse fine : ℝ}
    (hd : 0<delta) (hr : 0<rho) (hlambda : 0 ≤ lambda) (hA : 0<A) (hB : 0 ≤ B)
    (hcoarse : (lambda*(delta^(2*eta)/16))/
      (A*delta^(-zeta)*(delta^(-seed)*rho^(-kappa))*(rho/2)^4) ≤ coarse)
    (hfine : fine ≤ (B*delta^(-zeta))/
      ((delta^t*(rho^2)^(-kappa))*(rho^2/2)^4)) :
    lambda*delta^(2*eta+2*zeta+seed+t)*rho^4*fine ≤ 16*A*B*rho^kappa*coarse := by
  have hlow := (div_le_iff₀ (show 0<A*delta^(-zeta)*(delta^(-seed)*rho^(-kappa))*(rho/2)^4 by positivity)).mp hcoarse
  have hhigh := (le_div_iff₀ (show 0<(delta^t*(rho^2)^(-kappa))*(rho^2/2)^4 by positivity)).mp hfine
  have hcross : (lambda*(delta^(2*eta)/16))*
      ((delta^t*(rho^2)^(-kappa))*(rho^2/2)^4)*fine ≤
      (B*delta^(-zeta))*(A*delta^(-zeta)*(delta^(-seed)*rho^(-kappa))*(rho/2)^4)*coarse := by
    calc
      _ = (lambda*(delta^(2*eta)/16))*(fine*((delta^t*(rho^2)^(-kappa))*(rho^2/2)^4)) := by ring
      _ ≤ (lambda*(delta^(2*eta)/16))*(B*delta^(-zeta)) := mul_le_mul_of_nonneg_left hhigh (by positivity)
      _ ≤ (coarse*(A*delta^(-zeta)*(delta^(-seed)*rho^(-kappa))*(rho/2)^4))*(B*delta^(-zeta)) :=
        mul_le_mul_of_nonneg_right hlow (by positivity)
      _ = _ := by ring
  have hsquare : (rho^2)^(-kappa)=rho^(-2*kappa) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr.le]
    congr 1
    norm_num
  have hleftR : 16*((rho^2)^(-kappa)*(rho^2/2)^4*rho^(2*kappa-4))=rho^4 := by
    calc
      _ = (rho^(-2*kappa)*rho^(8:ℝ))*rho^(2*kappa-4) := by rw [hsquare,Real.rpow_ofNat]; ring
      _ = rho^((-2*kappa+8)+(2*kappa-4)) := by rw [←Real.rpow_add hr,←Real.rpow_add hr]
      _ = rho^4 := by rw [show (-2*kappa+8)+(2*kappa-4)=(4:ℝ) by ring,Real.rpow_ofNat]
  have hrightR : 16*(rho^(-kappa)*(rho/2)^4*rho^(2*kappa-4))=rho^kappa := by
    calc
      _ = (rho^(-kappa)*rho^(4:ℝ))*rho^(2*kappa-4) := by rw [Real.rpow_ofNat]; ring
      _ = rho^((-kappa+4)+(2*kappa-4)) := by rw [←Real.rpow_add hr,←Real.rpow_add hr]
      _ = rho^kappa := by congr 1; ring
  have hleftD : delta^(2*eta)*delta^t*delta^(2*zeta+seed)=delta^(2*eta+2*zeta+seed+t) := by
    rw [←Real.rpow_add hd,←Real.rpow_add hd]
    congr 1
    ring
  have hrightD : delta^(-zeta)*delta^(-zeta)*delta^(-seed)*delta^(2*zeta+seed)=1 := by
    rw [←Real.rpow_add hd,←Real.rpow_add hd,←Real.rpow_add hd]
    rw [show -zeta+-zeta+-seed+(2*zeta+seed)=(0:ℝ) by ring,Real.rpow_zero]
  have hh := mul_le_mul_of_nonneg_left hcross
    (show 0 ≤ 256*delta^(2*zeta+seed)*rho^(2*kappa-4) by positivity)
  have hLeft : (256*delta^(2*zeta+seed)*rho^(2*kappa-4))*
      ((lambda*(delta^(2*eta)/16))*((delta^t*(rho^2)^(-kappa))*(rho^2/2)^4)*fine)=
        lambda*delta^(2*eta+2*zeta+seed+t)*rho^4*fine := by
    calc
      _ = lambda*(delta^(2*eta)*delta^t*delta^(2*zeta+seed))*
        (16*((rho^2)^(-kappa)*(rho^2/2)^4*rho^(2*kappa-4)))*fine := by ring
      _ = _ := by rw [hleftD,hleftR]
  have hRight : (256*delta^(2*zeta+seed)*rho^(2*kappa-4))*
      ((B*delta^(-zeta))*(A*delta^(-zeta)*(delta^(-seed)*rho^(-kappa))*(rho/2)^4)*coarse)=
        16*A*B*rho^kappa*coarse := by
    calc
      _ = 16*A*B*(delta^(-zeta)*delta^(-zeta)*delta^(-seed)*delta^(2*zeta+seed))*
        (16*(rho^(-kappa)*(rho/2)^4*rho^(2*kappa-4)))*coarse := by ring
      _ = _ := by rw [hrightD,hrightR]; ring
  rwa [hLeft,hRight] at hh

/-- Fixed geometric coefficient in the terminal raw point-ratio consumer. -/
def pointRatioConstant : ℝ :=
  16*(2051:ℝ)^4*(373248*64^3*NativeOriginalPrunedMass.volumeConstant)*43*2401

lemma pointRatioConstant_pos : 0<pointRatioConstant := by
  have hp := NativeOriginalPrunedMass.volumeConstant_pos
  unfold pointRatioConstant
  positivity

/-- The actual source supplies the coarse retained raw lower and squared
fine raw upper. The coarse multiplicity uses scheduled reference uniformity
and seed balance, avoiding the depth0 parent tax and hereditary3tau loss.
No raw profile or point-count ratio is an input. -/
theorem source_squared_raw_ratio {n d g level : ℕ} {D : FiniteScaleSource n}
    {eta zeta a seed t : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n))
    (E1 E2 : Finset (Fin n × Index)) (h21 : E2⊆E1) (hE2ne : E2.Nonempty)
    (L : ℕ) (schedule : Fin g → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (Hcore : IsCore D original R a eta zeta (menuSize d g) g L
      (relationMenu h R a schedule Rel) (fun j => 2^(schedule j).val) E1)
    (j : Fin g) (hm6 : 6 ≤ (schedule j).val)
    (hb : phaseDepth (schedule j).val ≤ level) (hsmall : D.thickness ≤ 1/8)
    (HB : HasBalancedScale h R E1 a level (schedule j).val seed)
    (HM : HasMiddleScale h R E1 a level (phaseDepth (schedule j).val) t)
    (G : ℕ) (hG : 0<G) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hret : lambda*(E1.card:ℝ) ≤ (G:ℝ)*E2.card) :
    let m := (schedule j).val
    let rho := 64/((2^m:ℕ):ℝ)
    lambda*D.thickness^(2*eta+2*zeta+seed+t)*rho^4*(rawPointCount D E2 (phaseDepth m):ℝ) ≤
      pointRatioConstant*(factor (menuSize d g) g L:ℝ)*G*(coreRadix original R L:ℝ)^4*
        rho^NativeFixedCompactKakeyaExponent.extremalExponent*(rawPointCount D E2 m:ℝ) := by
  obtain ⟨horiginal,hdy,ha,_hRn,_hcard,_hshade,_hden,_hCW,Hpop⟩ := Hbackbone
  let m := (schedule j).val
  let b := phaseDepth m
  let rho : ℝ := 64/((2^m:ℕ):ℝ)
  let F1 := factor (menuSize d g) g L
  let Q1 := coreRadix original R L
  let A : ℝ := (F1:ℝ)*G*43*2401*(Q1:ℝ)^4
  let B : ℝ := (2051:ℝ)^4*(373248*64^3*NativeOriginalPrunedMass.volumeConstant)
  have hd := h.1.2.1
  have hr : 0<rho := by dsimp [rho]; positivity
  have hE1old : E1⊆incidences original := Hcore.1.trans (filter_subset _ _)
  have hE2ret : E2⊆NativeCoarseShadingCapacity.retained original R := h21.trans Hcore.1
  have hF1 : 0<F1 := by
    obtain ⟨z,hz⟩ := Hcore.2.1
    have hi : 0<(incidences original).card := card_pos.mpr ⟨z,hE1old hz⟩
    have hh := Hcore.2.2.1
    change (incidences original).card ≤ F1*E1.card at hh
    by_contra hf
    have he : F1=0 := Nat.eq_zero_of_not_pos hf
    rw [he,zero_mul] at hh
    omega
  have hQ1 : 0<Q1 := lt_of_lt_of_le (by norm_num : 0<4)
    (NativeSourceSizeBounds.radix_four_le (NativeOriginalParentDensityCore.retained original R).card L)
  have hA : 0<A := by dsimp [A]; positivity
  have hB : 0<B := by
    have hp := NativeOriginalPrunedMass.volumeConstant_pos
    dsimp [B]
    positivity
  have hm : m ≤ level := Nat.le_of_lt_succ (schedule j).isLt
  have hb6 : 6 ≤ b := by dsimp [b,phaseDepth,m]; omega
  have hmesh (d' : ℕ) : 32/((2^d':ℕ):ℝ)=(64/((2^d':ℕ):ℝ))/2 := by ring
  have hRet := two_stage_incidence_retention original E1 E2 F1 G lambda hlambda Hcore.2.2.1 hret
  have hMu := retained_scheduled_full_upper h original R E1 E2 h21 L schedule Rel Hcore j HB
  have hLow := raw_point_lower_with_retention h original horiginal ha R E2 hE2ret hE2ne level m hdy hm
    (fun p hp => (Hpop ⟨m,Nat.lt_succ_of_le hm⟩ p hp).2) lambda ((F1:ℝ)*G)
    ((Q1:ℝ)^4*(D.thickness^(-seed)*rho^(-NativeFixedCompactKakeyaExponent.extremalExponent)))
    hlambda (by positivity) (by positivity) hRet hMu
  have hLow' := (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (original_shading_mass_lower h original horiginal hsmall) hlambda)
      (by positivity)).trans hLow
  rw [hmesh m] at hLow'
  have hCoarse : (lambda*(D.thickness^(2*eta)/16))/
      (A*D.thickness^(-zeta)*(D.thickness^(-seed)*rho^(-NativeFixedCompactKakeyaExponent.extremalExponent))*(rho/2)^4) ≤
        (rawPointCount D E2 m:ℝ) := by
    simpa only [A,rho,mul_assoc,mul_comm,mul_left_comm] using hLow'
  have hFine1 := raw_point_upper h original horiginal ha R E1 Hcore.1 Hcore.2.1 level b hdy hb hb6
    (fun p hp => (Hpop ⟨b,Nat.lt_succ_of_le hb⟩ p hp).1)
    (D.thickness^t*(64/((2^b:ℕ):ℝ))^(-NativeFixedCompactKakeyaExponent.extremalExponent))
    (by positivity) HM.1
  have hFine2 : (rawPointCount D E2 b:ℝ) ≤ (rawPointCount D E1 b:ℝ) := by
    exact_mod_cast raw_point_count_mono D E1 E2 h21 b
  have hFine := hFine2.trans hFine1
  rw [hmesh b,squared_scale_identity m hm6] at hFine
  have hFine' : (rawPointCount D E2 b:ℝ) ≤ (B*D.thickness^(-zeta))/
      ((D.thickness^t*(rho^2)^(-NativeFixedCompactKakeyaExponent.extremalExponent))*(rho^2/2)^4) := hFine
  have hh := squared_profile_cross hd hr hlambda hA hB.le hCoarse hFine'
  apply hh.trans_eq
  dsimp [A,B,F1,Q1,pointRatioConstant]
  ring

/-- A genuine squared stop stays in the same middle window. The lower
endpoint only needs the original stop's proved positive-depth margin. -/
lemma squared_depth_in_middle (w : ℝ) (hw : w ≤ 1/2) (m level : ℕ)
    (hm6 : 6 ≤ m) (hstop : m ≤ level/4) (hlo : w*(level:ℝ) ≤ m) :
    w*(level:ℝ) ≤ phaseDepth m ∧ (phaseDepth m:ℝ) ≤ (1-w)*(level:ℝ) := by
  have hmb : m ≤ phaseDepth m := by dsimp [phaseDepth]; omega
  have hmbR : (m:ℝ) ≤ phaseDepth m := by exact_mod_cast hmb
  have hb : phaseDepth m ≤ 2*m := Nat.sub_le _ _
  have hbR : (phaseDepth m:ℝ) ≤ 2*(m:ℝ) := by exact_mod_cast hb
  have hfour : 4*m ≤ level := by omega
  have hfourR : 4*(m:ℝ) ≤ level := by exact_mod_cast hfour
  have hwL := mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg level)
  exact ⟨hlo.trans hmbR,by nlinarith⟩

/-- Direct consumer of the original source's all-middle field, rather than
an assumed raw profile. Only its already available stop-depth bounds enter. -/
theorem source_squared_raw_ratio_of_middle_window {n d g level : ℕ} {D : FiniteScaleSource n}
    {eta zeta a seed t : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n))
    (E1 E2 : Finset (Fin n × Index)) (h21 : E2⊆E1) (hE2ne : E2.Nonempty)
    (L : ℕ) (schedule : Fin g → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (Hcore : IsCore D original R a eta zeta (menuSize d g) g L
      (relationMenu h R a schedule Rel) (fun j => 2^(schedule j).val) E1)
    (j : Fin g) (hm6 : 6 ≤ (schedule j).val) (hstop : (schedule j).val ≤ level/4)
    (hsmall : D.thickness ≤ 1/8)
    (HB : HasBalancedScale h R E1 a level (schedule j).val seed)
    (w : ℝ) (hw : w ≤ 1/2) (hlo : w*(level:ℝ) ≤ (schedule j).val)
    (HM : ∀k : ℕ,w*(level:ℝ) ≤ k → (k:ℝ) ≤ (1-w)*(level:ℝ) → HasMiddleScale h R E1 a level k t)
    (G : ℕ) (hG : 0<G) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hret : lambda*(E1.card:ℝ) ≤ (G:ℝ)*E2.card) :
    let m := (schedule j).val
    let rho := 64/((2^m:ℕ):ℝ)
    lambda*D.thickness^(2*eta+2*zeta+seed+t)*rho^4*(rawPointCount D E2 (phaseDepth m):ℝ) ≤
      pointRatioConstant*(factor (menuSize d g) g L:ℝ)*G*(coreRadix original R L:ℝ)^4*
        rho^NativeFixedCompactKakeyaExponent.extremalExponent*(rawPointCount D E2 m:ℝ) := by
  have hwindow := squared_depth_in_middle w hw (schedule j).val level hm6 hstop hlo
  have hb := (phaseDepth_bounds (schedule j).val (schedule j).val level hm6 le_rfl hstop).2
  exact source_squared_raw_ratio h original R E1 E2 h21 hE2ne L schedule Rel Hbackbone Hcore j hm6 hb hsmall
    HB (HM _ hwindow.1 hwindow.2) G hG lambda hlambda hret

/-- The queried weighted vertices are exactly the raw occupied cell image,
by composition of the two literal image maps. -/
lemma vertices_card_eq_rawPointCount {n : ℕ} (D : FiniteScaleSource n)
    (E : Finset (Fin n × Index)) (m : ℕ) :
    (NativeQueriedVertexWeights.vertices E (NativeSpatialAngularGeometry.spatialLabel D (2^m))).card=
      rawPointCount D E m := by
  rw [NativeQueriedVertexWeights.vertices,Finset.image_image]
  rfl

end NativeRawPointRankFourRatio
