import Theorems.Thm_StickyKakeya4_native_raw_point_source_profiles
import Theorems.Thm_StickyKakeya4_native_two_scale_configuration
import Theorems.Thm_StickyKakeya4_native_conditional_coarse_interpolation
import Theorems.Thm_StickyKakeya4_native_endpoint_parent_bounds
import Theorems.Thm_StickyKakeya4_native_all_two_scale_configuration
import Theorems.Thm_StickyKakeya4_native_hereditary_scale_upper
import Theorems.Thm_StickyKakeya4_native_two_axis_conditional_transfer

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeRawPointGlobalProfiles
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeCoarseShadingCapacity NativeCoarsePointMultiplicity
open NativeSpatialAngularGeometry NativeRawShadowPointComparison NativeFullCoarseShadow
open NativeCoarseDyadicShading NativeCoarseDirectionThinning NativeCoarseShadingPruning
open NativeSameSourceCoarseSelection NativeMiddleWindowBalance NativeRawPointSourceProfiles
open scoped BigOperators ENNReal

open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations NativeDyadicParentCells
open NativeConditionalCoarseInterpolation NativeIncidenceMultiplicityTower NativeEndpointParentBounds

/-- Aggregate the actual conditional shadows over the original depth0
parents. The only cost is their ORIGINAL AD population bound. -/
theorem global_shadow_multiplicity_upper {n : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (hR : ∀z∈E,z.1∈R) (level m : ℕ)
    (Hpop : ∀p,(R.filter (fun i => parentLabel D a 1 i=p)).Nonempty →
      D.thickness^zeta*((1:ℝ)/D.thickness)^3  ≤ 
        ((R.filter (fun i => parentLabel D a 1 i=p)).card:ℝ))
    (U : ℝ) (hU : 0 ≤ U)
    (HU : ∀p,(parentEdges D a 1 E p).Nonempty →
      (NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level m (parentEdges D a 1 E p))).toReal ≤ U) :
    (NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level m E)).toReal ≤ 
      (373248*D.thickness^(-zeta))*U := by
  let I := E.image (physicalPair h R a level m)
  have hchild : ∀q∈I.image (fun z => ancestor m 0 z.1),
      NativeIncidenceMultiplicityTower.multiplicity (parent I (ancestor m 0) q) ≤ U := by
    intro q hq
    have hn := parent_nonempty I (ancestor m 0) hq
    change (parent (E.image (physicalPair h R a level m)) (ancestor m 0) q).Nonempty at hn
    rw [←physical_image_parent h R E a level 0 m (Nat.zero_le _) q] at hn
    have hqn : (parentEdges D a 1 E q).Nonempty := by
      simpa using image_nonempty.mp hn
    have hh := HU q hqn
    have hmu := NativeTwoAxisConditionalTransfer.conditional_full_eq_image h R E a level 0 m hR q
    simp only [pow_zero] at hmu
    rw [hmu] at hh
    change NativeIncidenceMultiplicityTower.multiplicity
      (parent (E.image (physicalPair h R a level m)) (ancestor m 0) q) ≤ U
    rw [←physical_image_parent h R E a level 0 m (Nat.zero_le _) q]
    simpa only [pow_zero] using hh
  have hsub : I.image (fun z => ancestor m 0 z.1)⊆R.image (parentLabel D a 1) := by
    intro p hp
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hp
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hv
    have he := parent_ancestor_eq D a (Nat.zero_le m) z.1
    rw [physicalPair_parent,he]
    simpa using mem_image_of_mem (parentLabel D a 1) (hR z hz)
  have hcount : ((I.image (fun z => ancestor m 0 z.1)).card:ℝ) ≤ 373248*D.thickness^(-zeta) := by
    have hp := NativeCoarsePruningBudget.original_occupied_count h R 1 (by norm_num) (by
      intro p hp
      simpa using Hpop p hp)
    have hc : ((I.image (fun z => ancestor m 0 z.1)).card:ℝ) ≤ (R.image (parentLabel D a 1)).card := by
      exact_mod_cast card_le_card hsub
    exact hc.trans (by simpa using hp)
  have hparent := multiplicity_le_tube_card (NativeIncidenceMultiplicityTower.coarse I (ancestor m 0))
  rw [coarse_parents] at hparent
  have hh := (multiplicity_le_parent_upper I (ancestor m 0) U hchild).trans
    (mul_le_mul_of_nonneg_left (hparent.trans hcount) hU)
  rw [full_source_multiplicity_real h R a level m E hR]
  exact hh.trans_eq (by ring)

/-- Conditional lower multiplicities also aggregate on the actual point
union, without a uniformity assumption or a loss in the number of parents. -/
theorem global_shadow_multiplicity_lower {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (hE : E.Nonempty) (hR : ∀z∈E,z.1∈R) (level m : ℕ)
    (L : ℝ) (hL : 0 ≤ L)
    (HL : ∀p,(parentEdges D a 1 E p).Nonempty →
      L ≤ (NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level m (parentEdges D a 1 E p))).toReal) :
    L ≤ (NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level m E)).toReal := by
  rw [full_source_multiplicity_real h R a level m E hR]
  change L ≤ NativeIncidenceMultiplicityTower.multiplicity (E.image (physicalPair h R a level m))
  apply NativeScaleMenuSuccessor.partition_multiplicity_lower _ (ancestor m 0) L hL (hE.image _)
  intro p hp
  have hn := parent_nonempty (E.image (physicalPair h R a level m)) (ancestor m 0) hp
  rw [←physical_image_parent h R E a level 0 m (Nat.zero_le _) p] at hn ⊢
  have hpn : (parentEdges D a 1 E p).Nonempty := by
    simpa using image_nonempty.mp hn
  have hh := HL p hpn
  have hmu := NativeTwoAxisConditionalTransfer.conditional_full_eq_image h R E a level 0 m hR p
  simp only [pow_zero] at hmu
  rw [hmu] at hh
  simpa only [pow_zero] using hh

/-- The all-two-scale source supplies global shadow powers at EVERY depth
by taking its existing outer-depth0 field. The finite parent loss is explicit. -/
theorem global_shadow_bounds_of_conditional {n : ℕ} {D : FiniteScaleSource n} {eta a zeta tau : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (hE : E.Nonempty) (hR : ∀z∈E,z.1∈R) (level m : ℕ)
    (Hpop : ∀p,(R.filter (fun i => parentLabel D a 1 i=p)).Nonempty →
      D.thickness^zeta*((1:ℝ)/D.thickness)^3  ≤ 
        ((R.filter (fun i => parentLabel D a 1 i=p)).card:ℝ))
    (HC : NativeTwoScaleConfiguration.HasConditionalTwoScale h R E a level 0 m tau) :
    let relative := 1/((2^m:ℕ):ℝ)
    D.thickness^tau*relative^(-NativeFixedCompactKakeyaExponent.extremalExponent) ≤ 
      (NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level m E)).toReal ∧
    (NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level m E)).toReal ≤ 
      (373248*D.thickness^(-zeta))*(D.thickness^(-tau)*relative^(-NativeFixedCompactKakeyaExponent.extremalExponent)) := by
  have hd := h.1.2.1
  have he : (64/((2^m:ℕ):ℝ))/(64/((1:ℕ):ℝ))=1/((2^m:ℕ):ℝ) := by norm_num; ring
  change ∀p,(parentEdges D a (2^0) E p).Nonempty → _ at HC
  simp only [pow_zero] at HC
  dsimp only
  constructor
  · apply global_shadow_multiplicity_lower h R E hE hR level m _ (by positivity)
    intro p hp
    have hh := (HC p hp).1
    simpa only [he] using hh
  · apply global_shadow_multiplicity_upper h R E hR level m Hpop _ (by positivity)
    intro p hp
    have hh := (HC p hp).2
    simpa only [he] using hh

/-- The actual original shading mass has an explicit native lower power.
This follows from native carrier counts and literal original-cell density. -/
lemma original_shading_mass_lower {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (hsmall : D.thickness ≤ 1/8) :
    D.thickness^(2*eta)/16 ≤ (wzTotalShadingVolume D).toReal := by
  have hd := h.1.2.1
  have hcard := ENNReal.toReal_mono (show (n:ℝ≥0∞)≠⊤ by finiteness)
    (NativeFiniteKakeyaCounts.carrier_count_lower h)
  simp only [ENNReal.rpow_eq_pow,←ENNReal.toReal_rpow,ENNReal.toReal_ofReal hd.le,
    ENNReal.toReal_natCast] at hcard
  have hinc := NativeLocalPairFibers.original_incidence_lower_weak h original horiginal hsmall
  have hbase : D.thickness^eta*D.thickness^(eta-3) ≤ D.thickness*(incidences original).card :=
    (mul_le_mul_of_nonneg_left hcard (Real.rpow_pos_of_pos hd _).le).trans hinc
  have hpower : (D.thickness^eta*D.thickness^(eta-3))*D.thickness^3=D.thickness^(2*eta) := by
    rw [←Real.rpow_natCast,←Real.rpow_add hd,←Real.rpow_add hd]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  have hh := mul_le_mul_of_nonneg_right hbase (show 0 ≤ D.thickness^3/16 by positivity)
  rw [total_shading_eq_incidence_volume D (half_pos hd) original horiginal]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (half_pos hd).le]
  calc
    _ = (D.thickness^eta*D.thickness^(eta-3))*(D.thickness^3/16) := by rw [←hpower]; ring
    _  ≤  (D.thickness*(incidences original).card)*(D.thickness^3/16) := hh
    _ = _ := by ring

/-- E1 has actual global raw point upper and lower profiles at every
physical dyadic depth6 ≤ m ≤ level, including the distinct squared depth2m-6.
Every original-delta power and finite constant is left visible. -/
theorem all_depth_raw_point_profile {n : ℕ} {D : FiniteScaleSource n} {eta a zeta tau : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆NativeCoarseShadingCapacity.retained original R)
    (hEn : E.Nonempty) (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hm : m ≤ level) (h6 : 6 ≤ m) (hsmall : D.thickness ≤ 1/8) (F : ℕ) (hF : 0<F)
    (hret : (incidences original).card ≤ F*E.card)
    (H : ∀b : ℕ,b ≤ level → ∀p,(R.filter (fun i => parentLabel D a (2^b) i=p)).Nonempty →
      D.thickness^zeta*((1/((2^b:ℕ):ℝ))/D.thickness)^3  ≤ 
        ((R.filter (fun i => parentLabel D a (2^b) i=p)).card:ℝ) ∧
      ((R.filter (fun i => parentLabel D a (2^b) i=p)).card:ℝ)  ≤ 
        D.thickness^(-zeta)*((1/((2^b:ℕ):ℝ))/D.thickness)^3)
    (HC : NativeTwoScaleConfiguration.HasConditionalTwoScale h R E a level 0 m tau) :
    let rho := 64/((2^m:ℕ):ℝ)
    let power := (1/((2^m:ℕ):ℝ))^(-NativeFixedCompactKakeyaExponent.extremalExponent)
    (D.thickness^(2*eta)/16)/
      ((F:ℝ)*43*D.thickness^(-zeta)*((373248*D.thickness^(-zeta))*(D.thickness^(-tau)*power))*
        2401*(rho/2)^4)  ≤  (rawPointCount D E m:ℝ) ∧
    (rawPointCount D E m:ℝ)  ≤ 
      ((2051:ℝ)^4*(373248*64^3*NativeOriginalPrunedMass.volumeConstant)*D.thickness^(-zeta))/
        ((D.thickness^tau*power)*(rho/2)^4) := by
  have hd := h.1.2.1
  have hER : ∀z∈E,z.1∈R := fun z hz => ((retained_spec original R z).mp (hE hz)).1
  have H0 : ∀p,(R.filter (fun i => parentLabel D a 1 i=p)).Nonempty →
      D.thickness^zeta*((1:ℝ)/D.thickness)^3  ≤ 
        ((R.filter (fun i => parentLabel D a 1 i=p)).card:ℝ) := by
    intro p hp
    simpa using (H 0 (Nat.zero_le _) p hp).1
  have HB := global_shadow_bounds_of_conditional h R E hEn hER level m H0 HC
  have hmsh : (64/((2^m:ℕ):ℝ))/2=32/((2^m:ℕ):ℝ) := by ring
  dsimp only
  rw [hmsh]
  constructor
  · have hh := raw_point_lower_with_retention h original horiginal ha R E hE hEn level m hdy hm
      (fun p hp => (H m hm p hp).2) 1 F _ (by norm_num) (by exact_mod_cast hF)
      (by positivity) (by simpa only [one_mul] using (show ((incidences original).card:ℝ) ≤ (F:ℝ)*E.card by exact_mod_cast hret)) HB.2
    simp only [one_mul] at hh
    exact (div_le_div_of_nonneg_right (original_shading_mass_lower h original horiginal hsmall)
      (by positivity)).trans hh
  · exact raw_point_upper h original horiginal ha R E hE hEn level m hdy hm h6
      (fun p hp => (H m hm p hp).1) _ (by positivity) HB.1

/-- Literal raw-image inclusion is the valid E1-to-E2 upper transfer. -/
lemma raw_point_count_mono {n : ℕ} (D : FiniteScaleSource n)
    (E1 E2 : Finset (Fin n × Index)) (h21 : E2⊆E1) (m : ℕ) :
    rawPointCount D E2 m ≤ rawPointCount D E1 m := card_le_card (image_subset_image h21)

/-- E2's raw lower profile uses its literal lambda/(F1 G) retention and the
already-derived hereditary conditional upper. No E1 lower multiplicity is
asserted for E2; the unchanged full R supplies the original parent-count tax. -/
theorem retained_raw_point_lower {n : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E1 E2 : Finset (Fin n × Index))
    (hE2 : E2⊆NativeCoarseShadingCapacity.retained original R) (hEn : E2.Nonempty)
    (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m ≤ level)
    (hsmall : D.thickness ≤ 1/8) (F1 G : ℕ) (hF1 : 0<F1) (hG : 0<G)
    (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hfirst : (incidences original).card ≤ F1*E1.card)
    (hsecond : lambda*(E1.card:ℝ) ≤ (G:ℝ)*E2.card)
    (H : ∀b : ℕ,b ≤ level → ∀p,(R.filter (fun i => parentLabel D a (2^b) i=p)).Nonempty →
      D.thickness^zeta*((1/((2^b:ℕ):ℝ))/D.thickness)^3  ≤ 
        ((R.filter (fun i => parentLabel D a (2^b) i=p)).card:ℝ) ∧
      ((R.filter (fun i => parentLabel D a (2^b) i=p)).card:ℝ)  ≤ 
        D.thickness^(-zeta)*((1/((2^b:ℕ):ℝ))/D.thickness)^3)
    (U : ℝ) (hU : 0<U)
    (HU : ∀p,(parentEdges D a 1 E2 p).Nonempty →
      (NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level m (parentEdges D a 1 E2 p))).toReal ≤ U) :
    (lambda*(D.thickness^(2*eta)/16))/
      (((F1:ℝ)*G)*43*D.thickness^(-zeta)*((373248*D.thickness^(-zeta))*U)*2401*
        (32/((2^m:ℕ):ℝ))^4)  ≤  (rawPointCount D E2 m:ℝ) := by
  have hd := h.1.2.1
  have hER : ∀z∈E2,z.1∈R := fun z hz => ((retained_spec original R z).mp (hE2 hz)).1
  have H0 : ∀p,(R.filter (fun i => parentLabel D a 1 i=p)).Nonempty →
      D.thickness^zeta*((1:ℝ)/D.thickness)^3  ≤ 
        ((R.filter (fun i => parentLabel D a 1 i=p)).card:ℝ) := by
    intro p hp
    simpa using (H 0 (Nat.zero_le _) p hp).1
  have hUpper := global_shadow_multiplicity_upper h R E2 hER level m H0 U hU.le HU
  have hret := two_stage_incidence_retention original E1 E2 F1 G lambda hlambda hfirst hsecond
  have hh := raw_point_lower_with_retention h original horiginal ha R E2 hE2 hEn level m hdy hm
    (fun p hp => (H m hm p hp).2) lambda ((F1:ℝ)*G) _ hlambda (by positivity)
    (by positivity) hret hUpper
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (original_shading_mass_lower h original horiginal hsmall) hlambda)
      (by positivity)).trans hh

/-- The actual all-two-scale source fields imply the hereditary conditional
upper needed by the E2 count. Its true fullSchedule has window at mosttau/16000;
the original transfer cost supplies both constant budgets. -/
theorem source_hereditary_conditional_upper {n : ℕ} {D : FiniteScaleSource n}
    {eta a seed tau : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (heta : 0 ≤ eta)
    (htau : 0 < tau) (hseed : seed ≤ tau/16384)
    (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index))
    (hE : E⊆incidences original) (hER : ∀z∈E,z.1∈R)
    (level : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (g F Q : ℕ) (hg : 0<g) (hgl : g ≤ level) (hF : 0<F) (hQ : 1 ≤ Q)
    (hgrid : 1/(g:ℝ) < min (NativeAllTwoScaleConfiguration.boundaryWindow tau) ((tau/16)/1000)/4)
    (hcost : (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-(seed/8)))
    (HU : ∀i j : Fin (g+1),
      HasUniformFibers E Q (NativeConditionedPairMenu.conditionedGlobalPair h R a level
        (NativeAllTwoScaleConfiguration.fullSchedule tau htau g level i).val
        (NativeAllTwoScaleConfiguration.fullSchedule tau htau g level j).val) ∧
      HasUniformFibers E Q (NativeConditionedPairMenu.conditionedGlobalPoint h R a level
        (NativeAllTwoScaleConfiguration.fullSchedule tau htau g level i).val
        (NativeAllTwoScaleConfiguration.fullSchedule tau htau g level j).val))
    (HC : ∀m f : ℕ,m ≤ f → f ≤ level →
      NativeTwoScaleConfiguration.HasConditionalTwoScale h R E a level m f tau) :
    ∀S⊆E,∀m f : ℕ,m ≤ f → f ≤ level → ∀p : Parent,
      (NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level f (parentEdges D a (2^m) S p))).toReal ≤
        D.thickness^(-(3*tau))*
          ((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-NativeFixedCompactKakeyaExponent.extremalExponent) := by
  let w := min (NativeAllTwoScaleConfiguration.boundaryWindow tau) ((tau/16)/1000)
  have hw : 0<w := lt_min (NativeAllTwoScaleConfiguration.boundaryWindow_pos htau) (by positivity)
  have hw8 : w ≤ 1/8 := (min_le_left _ _).trans
    (show NativeAllTwoScaleConfiguration.boundaryWindow tau ≤ 1/8 from min_le_right _ _)
  have hwloss : w ≤ tau/16000 := by
    have hh : w ≤ (tau/16)/1000 := min_le_right _ _
    linarith
  have hlarge : 4 ≤ w*(level:ℝ) := large_level_of_grid w hw g level hg hgrid hgl
  have hbudgets := NativeHereditaryScaleUpper.reference_cost_budgets
    h.1.2.1 h.1.2.2.1 heta htau.le F Q hF hQ (show 2*(seed/8) ≤ tau/4 by linarith) hcost
  apply NativeHereditaryScaleUpper.hereditary_three_loss h original horiginal ha R E hE hER level hdy
    NativeFixedCompactKakeyaExponent.extremalExponent_nonneg
    NativeFixedCompactKakeyaExponent.extremalExponent_le_three htau hw hw8 hwloss
    g Q hg hgl hgrid hlarge hbudgets.1 hbudgets.2
  · intro i j
    exact HU i j
  · intro i j hij p hp
    exact (NativeTwoAxisConditionalTransfer.scheduled_image_bounds h R E a level
      (NativeFixedSizeScaleMenu.windowSchedule w hw.le g level i).val
      (NativeFixedSizeScaleMenu.windowSchedule w hw.le g level j).val tau hER
      (HC _ _ hij (Nat.le_of_lt_succ (NativeFixedSizeScaleMenu.windowSchedule w hw.le g level j).isLt)) p hp).2

end NativeRawPointGlobalProfiles
