import Theorems.Thm_StickyKakeya4_native_window_source_counts
import Theorems.Thm_StickyKakeya4_native_reference_slice_class_bounds
import Theorems.Thm_StickyKakeya4_native_variable_height_source_bridge
import Theorems.Thm_StickyKakeya4_native_variable_height_reference_counts

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeWindowSourceClasses
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeLocalPairFibers NativeCoarseShadingUniformity NativeCoarseDirectionThinning
open NativeJointUniformCoarseRelations NativeFixedCompactKakeyaExponent NativeMiddleWindowBalance
open NativeAnisotropicShortRowGeometry NativeColumnPopulationBounds NativeReferenceColumnExponents
open NativeVariableHeightPopulation NativeVariableHeightReferenceCounts NativeIncidenceMultiplicityTower

open NativeWindowSourceCounts NativeSliceClassAlgebra NativeReferenceSliceClassBounds NativeAnisotropicSliceLabels

/-- The complete common-window source class law. Actual original-source
profiles and queried rows produce the counts; the only class loss is the
installed Qref^4. The same true height b=fine-m+3 is kept throughout. -/
theorem queried_window_class_power_bounds {n level : ℕ} {D : FiniteScaleSource n}
    {eta eta2 zeta a lambda c1 c2 : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (HB : HasOriginalBackbone D original R a level zeta)
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R)
    (F1 F2 G Q1 Q2 : ℕ) (hF1 : 0 < F1) (hG : 0 < G) (hQ2 : 0 < Q2)
    (hQ1 : 1 ≤ Q1) (hGF : G ≤ F2) (heta2 : 0 ≤ eta2) (hlambda : 0 < lambda)
    (hRich : ∀e,e∈E → D.thickness^eta*(2^level:ℕ)/
      (16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) ≤
        (pairFiber D a (2^level) E (localPair D a (2^level) e)).card)
    (hcost1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c1))
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta2) ≤ D.thickness^(-c2))
    (m fine coarse : ℕ) (hm6 : 6 ≤ m) (hmc : m ≤ coarse) (hcf : coarse ≤ fine)
    (hFine : fine ≤ NativeSquaredGrainQueries.phaseDepth m)
    (hFineL : NativeSquaredGrainQueries.phaseDepth m ≤ level)
    (Hqueries : ∀s : ℕ,s=fine ∨ s=coarse →
      HasUniformFibers E Q2 (fixedPair D a level s s (representative h R a (2^s))) ∧
      HasUniformFibers E Q2 (fixedPair D a level s (max 6 (fine-m+3)) (representative h R a (2^s))))
    (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty)
    (population fullLower fullUpper : ℝ) (hpopulation : 0 < population)
    (hfullLower : 0 < fullLower) (hfullUpper : 0 < fullUpper)
    (hret : population*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E p).card)
    (Hfull : ∀s : ℕ,s=fine ∨ s=coarse →
      fullLower*(relativeWidth m s)^(-extremalExponent) ≤
        (NativeFiniteKakeyaCounts.multiplicity
          (NativeFullCoarseShadow.fullSource h R a level s (parentEdges D a (2^m) E p))).toReal ∧
      (NativeFiniteKakeyaCounts.multiplicity
          (NativeFullCoarseShadow.fullSource h R a level s (parentEdges D a (2^m) E p))).toReal ≤
        fullUpper*(relativeWidth m s)^(-extremalExponent))
    (HF : HasUniformFibers (parentEdges D a (2^m) E p) Q2
      (fun z => columnLabel D a (2^m) p (64/((2^fine:ℕ):ℝ)) (64/((2^(fine-m+3):ℕ):ℝ)) z.2))
    (HC : HasUniformFibers (parentEdges D a (2^m) E p) Q2
      (fun z => columnLabel D a (2^m) p (64/((2^coarse:ℕ):ℝ)) (64/((2^(fine-m+3):ℕ):ℝ)) z.2)) :
    let eps := lambda*D.thickness^(c1+3*c2)
    let C := NativeVariableHeightSourceBridge.comparisonCost
    let L := lowerCountCoefficient D.thickness zeta population ((C/eps)*fullUpper)
    let U := 8*(NativeVariableHeightNumeratorUpper.pairUpperConstant*D.thickness^(-2*zeta))/((eps/C)*fullLower)
    let T : ℝ := ((2^(fine-coarse):ℕ):ℝ)
    let Pf := NativeHeightWindowRelations.points D a m fine (fine-m+3) E p
    let Pc := NativeHeightWindowRelations.points D a m coarse (fine-m+3) E p
    ((L/U)*T^(3-extremalExponent)*Pc.card ≤ Pf.card ∧
      (Pf.card:ℝ) ≤ (U/L)*T^(3-extremalExponent)*Pc.card) ∧
    ∀x∈Pf,
      (L/((Q2:ℝ)^4*U))*T^(3-extremalExponent) ≤
        (Pf.filter (fun z => horizontalCoarsen fine coarse z=horizontalCoarsen fine coarse x)).card ∧
      ((Pf.filter (fun z => horizontalCoarsen fine coarse z=horizontalCoarsen fine coarse x)).card:ℝ) ≤
        (((Q2:ℝ)^4*U)/L)*T^(3-extremalExponent) := by
  intro eps C L U T Pf Pc
  have hmf := hmc.trans hcf
  have hgf := prepared_window_geometry m fine fine hm6 hmf hmf le_rfl hFine
  have hgc := prepared_window_geometry m fine coarse hm6 hmf hmc hcf hFine
  have Hfine := queried_window_point_power_bounds h original R HB E hE F1 F2 G Q1 Q2
    hF1 hG hQ2 hQ1 hGF heta2 hlambda hRich hcost1 hcost2 m fine (fine-m+3) hm6 hmf
    hgf.2.1 (hFine.trans hFineL) hgf.1 hgf.2.2 (Hqueries fine (Or.inl rfl)).1
    (Hqueries fine (Or.inl rfl)).2 p hp population fullLower fullUpper hpopulation hfullLower hfullUpper
    hret (Hfull fine (Or.inl rfl))
  have Hcoarse := queried_window_point_power_bounds h original R HB E hE F1 F2 G Q1 Q2
    hF1 hG hQ2 hQ1 hGF heta2 hlambda hRich hcost1 hcost2 m coarse (fine-m+3) hm6 hmc
    hgc.2.1 (hcf.trans (hFine.trans hFineL)) hgc.1 hgc.2.2 (Hqueries coarse (Or.inr rfl)).1
    (Hqueries coarse (Or.inr rfl)).2 p hp population fullLower fullUpper hpopulation hfullLower hfullUpper
    hret (Hfull coarse (Or.inr rfl))
  have hd := h.1.2.1
  have heps : 0 < eps := mul_pos hlambda (Real.rpow_pos_of_pos hd _)
  have hC : 0 < C := NativeVariableHeightSourceBridge.comparisonCost_pos
  have hPair := NativeVariableHeightNumeratorUpper.pairUpperConstant_pos
  have hL : 0 < L := by dsimp [L,lowerCountCoefficient]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hheight : (0:ℝ)<64/((2^(fine-m+3):ℕ):ℝ) := by positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have HPfine : L*(relativeWidth m fine)^(extremalExponent-3) ≤
      (64/((2^(fine-m+3):ℕ):ℝ))*(Pf.card:ℝ) ∧
      (64/((2^(fine-m+3):ℕ):ℝ))*(Pf.card:ℝ) ≤ U*(relativeWidth m fine)^(extremalExponent-3) := by
    simpa only [U,L,eps,C,Pf,mul_div_assoc] using Hfine
  have HPcoarse : L*(relativeWidth m coarse)^(extremalExponent-3) ≤
      (64/((2^(fine-m+3):ℕ):ℝ))*(Pc.card:ℝ) ∧
      (64/((2^(fine-m+3):ℕ):ℝ))*(Pc.card:ℝ) ≤ U*(relativeWidth m coarse)^(extremalExponent-3) := by
    simpa only [U,L,eps,C,Pc,mul_div_assoc] using Hcoarse
  constructor
  · exact global_count_ratio_bounds hheight (relativeWidth_pos m fine) hT
      (relativeWidth_ratio m fine coarse hcf) hL hU HPfine HPcoarse
  · intro x hx
    have hclasses := NativeHeightWindowRelations.horizontal_class_counts D a m fine coarse (fine-m+3) hcf E p Q2 HF HC
    have HPimage : L*(relativeWidth m coarse)^(extremalExponent-3) ≤
        (64/((2^(fine-m+3):ℕ):ℝ))*(Pf.image (horizontalCoarsen fine coarse)).card ∧
        (64/((2^(fine-m+3):ℕ):ℝ))*(Pf.image (horizontalCoarsen fine coarse)).card ≤
          U*(relativeWidth m coarse)^(extremalExponent-3) := by
      rw [NativeHeightWindowRelations.points_horizontal_coarsen D a m fine coarse (fine-m+3) hcf E p]
      exact HPcoarse
    have hh := class_bounds_from_global_counts Pf (horizontalCoarsen fine coarse) (Q2^4) (by positivity) hclasses
      (64/((2^(fine-m+3):ℕ):ℝ)) (relativeWidth m fine) (relativeWidth m coarse) T extremalExponent L U
      hheight (relativeWidth_pos m fine) hT (relativeWidth_ratio m fine coarse hcf) hL hU HPfine HPimage x hx
    simpa only [Nat.cast_pow] using hh

end NativeWindowSourceClasses
