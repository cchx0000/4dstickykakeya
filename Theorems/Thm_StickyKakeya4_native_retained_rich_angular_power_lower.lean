import Theorems.Thm_StickyKakeya4_native_saturated_angular_power_lower
import Theorems.Thm_StickyKakeya4_native_rich_angular_image_lower

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 9500000

noncomputable section
namespace NativeRetainedRichAngularPowerLower
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeOriginalCellChartGeometry
open NativeOriginalPointSaturation NativeOriginalPointAngularLower NativeSaturatedAngularPowerLower
open NativeIncidenceMultiplicityTower NativeLocalMenuInterpolation NativeJointUniformCoarseRelations
open NativeFixedCompactKakeyaExponent NativeCoarseFineMultiplicity NativeSaturatedPointAngularLower
open NativeActualAngularMenuLower NativeRichAngularImageLower NativeNormalizedCellAngularMenu RichDirectionalLayers

/-- Read the original reference mean through the one third core and an
already chosen rich angular class. Both point refinements, all original
edge weights and the sigma-menu denominator remain explicit. -/
theorem retained_rich_reference_power_lower {n J : ℕ} {D : FiniteScaleSource n}
    {eta a tau gap gamma : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E1 E2 S I T : Finset (Fin n × Index)) (h21 : E2⊆ E1) (hE1 : E1⊆ incidences original)
    (level m s c : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m≤ level)
    (hs : 3≤ s) (hf : m+s-3≤ level) (hcf : c≤ m+s-3)
    (hgap0 : 0≤ gap) (hgap : (((m+s-3)-c:ℕ):ℝ)≤ gap*level)
    (p : Parent) (HS : Saturated (parentEdges D a (2^m) E2 p) S Prod.snd)
    (hIS : I⊆ S) (hTI : T⊆ I) (F3 : ℕ) (hF3 : 0< F3) (hret3 : S.card≤ F3*I.card)
    (hgamma : 0≤ gamma)
    (hret : gamma*(parentEdges D a (2^m) E1 p).card≤ (parentEdges D a (2^m) E2 p).card)
    (Q1 Q2 Q3 : ℕ) (HRef : HasUniformFibers E1 Q1 (formalPair D a c))
    (HPoint2 : HasUniformFibers (parentEdges D a (2^m) E2 p) Q2 Prod.snd)
    (HPoint3 : HasUniformFibers I Q3 Prod.snd)
    (HProfiles : ∀d : ℕ,d≤ level → ∀t : Parent,(parentEdges D a (2^d) E1 t).Nonempty →
      D.thickness^tau*(localScale D.thickness d)^(-extremalExponent)≤ multiplicity (parentEdges D a (2^d) E1 t) ∧
      multiplicity (parentEdges D a (2^d) E1 t)≤ D.thickness^(-tau)*(localScale D.thickness d)^(-extremalExponent))
    (sigmaDepth : Fin J → ℕ) (j : Fin J) (k : Index) (hk : k∈I.image Prod.snd) (q : Fin 3 → ℤ)
    (hRich : ((I.filter (fun z => z.2=k)).card:ℝ)/
        (2*(J:ℝ)*(((I.filter (fun z => z.2=k)).image
          (fun z => angularCell D (2^m) (2^(sigmaDepth j)) p z.1)).card:ℝ)) <
      ((classFiber (T.filter (fun z => z.2=k))
        (fun z => angularCell D (2^m) (2^(sigmaDepth j)) p z.1) q).card:ℝ)) :
    gamma*D.thickness^(2*tau+3*gap)*(64/((2^s:ℕ):ℝ))^(-extremalExponent)≤
      (343*(Q1:ℝ)^2*(Q2:ℝ)^2)*(F3:ℝ)*(Q3:ℝ)^2*
        (2*(J:ℝ)*(((I.filter (fun z => z.2=k)).image
          (fun z => angularCell D (2^m) (2^(sigmaDepth j)) p z.1)).card:ℝ))*
        (((classFiber (T.filter (fun z => z.2=k))
          (fun z => angularCell D (2^m) (2^(sigmaDepth j)) p z.1) q).image
            (fun z => angularCell D (2^m) (2^s) p z.1)).card:ℝ) := by
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have hP21 : parentEdges D a (2^m) E2 p⊆ parentEdges D a (2^m) E1 p := filter_subset_filter _ h21
  have hIn : I.Nonempty := image_nonempty.mp ⟨k,hk⟩
  have hp1 : (parentEdges D a (2^m) E1 p).Nonempty := hIn.mono (hIS.trans (HS.1.trans hP21))
  have hLower := mul_le_mul_of_nonneg_left (HProfiles m hm p hp1).1 hgamma
  have hRet := retained_incidence_multiplicity _ _ hP21 hgamma hret
  have hLower' := hLower.trans hRet
  have hI1 : I⊆ E1 := hIS.trans (HS.1.trans ((filter_subset _ _).trans h21))
  have hscale : ((2^(m+s-3):ℕ):ℝ)*D.thickness≤ 1 := by
    rw [NativeLocalParentScales.relative_scale hdy hf]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  let U := D.thickness^(-tau)*(localScale D.thickness c)^(-extremalExponent)
  have hU : 0≤ U := by dsimp [U]; have hcpos := localScale_pos hd c; positivity
  have hRichFine := rich_class_angular_lower h original horiginal ha E1 I T hTI hI1 (hI1.trans hE1)
    m s c hs hcf hscale p Q1 HRef U hU (fun t ht => (HProfiles c (hcf.trans hf) t ht).2)
    sigmaDepth j k q hRich
  have hPointN : (I.filter (fun z => z.2=k)).Nonempty := by
    obtain ⟨z,hz,hzk⟩ := mem_image.mp hk
    exact ⟨z,mem_filter.mpr ⟨hz,hzk⟩⟩
  have hMenuPos : (0:ℝ)< ((I.filter (fun z => z.2=k)).image
      (fun z => angularCell D (2^m) (2^(sigmaDepth j)) p z.1)).card := by
    exact_mod_cast (hPointN.image _).card_pos
  have hJpos : (0:ℝ)< J := by exact_mod_cast (show 0< J by have hj := j.isLt; omega)
  have hDen : 0< 2*(J:ℝ)*(((I.filter (fun z => z.2=k)).image
      (fun z => angularCell D (2^m) (2^(sigmaDepth j)) p z.1)).card:ℝ) := by positivity
  have hWeight := (div_le_iff₀ hDen).mp hRichFine.le
  have hMean := mean_le_point_fiber I Q3 HPoint3 k hk
  have hRefMean := saturated_refined_multiplicity_lower _ S I HS hIS hIn Q2 F3 hF3 HPoint2 hret3
  have hFromMean := hRefMean.trans (mul_le_mul_of_nonneg_left hMean (by positivity))
  have hFromWeight := mul_le_mul_of_nonneg_left hWeight
    (show 0≤ ((Q2:ℝ)^2*F3)*(Q3:ℝ)^2 by positivity)
  let C : ℝ := (343*(Q1:ℝ)^2*(Q2:ℝ)^2)*(F3:ℝ)*(Q3:ℝ)^2*
    (2*(J:ℝ)*(((I.filter (fun z => z.2=k)).image
      (fun z => angularCell D (2^m) (2^(sigmaDepth j)) p z.1)).card:ℝ))*
    (((classFiber (T.filter (fun z => z.2=k))
      (fun z => angularCell D (2^m) (2^(sigmaDepth j)) p z.1) q).image
      (fun z => angularCell D (2^m) (2^s) p z.1)).card:ℝ)
  have hMeanBound : multiplicity (parentEdges D a (2^m) E2 p)≤ C*U := by
    apply hFromMean.trans
    simpa only [C,mul_assoc,mul_comm,mul_left_comm] using hFromWeight
  have hUUpper := ancestor_parent_power_upper (tau:=tau) hd hd1 extremalExponent_nonneg extremalExponent_le_three
    hgap0 level c (m+s-3) hdy hcf hgap
  have hCombined : gamma*(D.thickness^tau*(localScale D.thickness m)^(-extremalExponent))≤
      C*(D.thickness^(-(tau+3*gap))*(localScale D.thickness (m+s-3))^(-extremalExponent)) :=
    (hLower'.trans hMeanBound).trans (mul_le_mul_of_nonneg_left hUUpper (by dsimp [C]; positivity))
  exact cancel_parent_powers hd (localScale_pos hd m) (localScale_pos hd (m+s-3)) (by positivity)
    extremalExponent_nonneg hgamma (actual_angular_scale_ratio D.thickness m s hs) hCombined

end NativeRetainedRichAngularPowerLower
