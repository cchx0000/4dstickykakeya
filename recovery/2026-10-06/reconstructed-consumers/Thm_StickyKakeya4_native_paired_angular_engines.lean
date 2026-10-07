import Theorems.Thm_StickyKakeya4_native_retained_rich_all_mesh_lower
import Theorems.Thm_StickyKakeya4_native_paid_mesh_angular_bounds
import Theorems.Thm_StickyKakeya4_native_rich_angular_rank_payment
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
set_option diagnostics true
noncomputable section
namespace NativePairedAngularEngines
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeLocalMenuInterpolation
open NativeJointUniformCoarseRelations NativeMiddleWindowBalance NativeFixedSizeScaleMenu
open NativeActualMesoscopicRankConfiguration NativeAllTwoScaleConfiguration NativeRankExponentHierarchy
open NativeMiddleGrainParentBudget NativeGeneralRankScalarBudget NativeOriginalPointSaturation
open NativeSaturatedSourceAngularRankLower NativeScheduledAngularAncestor NativeGenericReferenceData
open NativeSourceSizeBounds NativeActivePhasePopulation NativeQueriedVertexWeights
open NativeOriginalPointAngularLower NativeSaturatedAngularPowerLower NativeFixedCompactKakeyaExponent
open NativeSaturatedAllMeshLower NativeRetainedRichAngularRankLower
open NativeNormalizedCellAngularMenu RichDirectionalLayers
open NativeRetainedRichAllMeshLower NativePaidMeshAngularBounds NativePaidMeshAngularUpper
open NativeExtraQueriedRankConfiguration NativeRichAngularRankPayment NativeNormalizedCellRelativeMenu
open NativeConditionalReferenceMenu NativeLocalParentGeometry

lemma rich_coefficient (g J : ℕ) :
    2*(2744*rowConstant*((g:ℝ)+1))*meshAngularConstant*(J:ℝ)=
      5488*rowConstant*((g:ℝ)+1)*(J:ℝ)*meshAngularConstant := by ring

/-- The actual source yields a paid rich-class lower at every final-mesh
angular scale. Its two-scale ratio has exponent exactly kappa. All third
refinement and sigma-menu costs are derived from the same Reference/E2
and the literal trim; no mean ratio or angular-AD certificate is an input. -/
theorem exists_paired_angular_engines (amin loss : ℝ)
    (hamin : 0< amin) (hloss : 0< loss) (hloss1 : loss≤ 1) :
    ∃(K : ℕ) (seedCap delta0 : ℝ),0< K ∧ 0< seedCap ∧ 0< delta0 ∧ delta0≤ 1/8 ∧
    (∀(n : ℕ) (D : FiniteScaleSource n) (eta zeta seed tau e : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta) (htau : 0< tau) (L g : ℕ),
        0≤ eta → 0≤ zeta → eta≤ seed/8 → zeta≤ seed/256 →
        seed≤ seedCap → D.thickness≤ delta0 →
      ∀ref : Reference h tau htau seed e zeta L g,
        HasCallerUniformities ref (factory g K) →
      ∀i : Fin (g+1),6≤ (ref.schedule i).val →
      let m := middleDepth (ref.schedule i).val
      ∀s : ℕ,6≤ s → s≤ m+6 →
      ∀r power : ℝ,0< r → r≤ D.thickness^power → amin≤ power →
        64*D.thickness≤ r^2 → 3072*r≤ ((64:ℝ)/((2^m:ℕ):ℝ))^2 →
      ∀(p : Parent) (E : Finset (Fin n × Index)),E⊆ ref.E1 →
        (∀z∈E,parentLabel D ref.a (2^m) z.1=p) →
      ∀cell : Index,
        (∀z∈E,physicalCell D ref.a (2^m) (2^s) p z.2=cell) →
        (((E.image (fun z => angularCell D (2^m) (2^s) p z.1)).card:ℝ)≤
          meshAngularConstant*r^(-loss)*(64/((2^s:ℕ):ℝ))^(-extremalExponent)) ∧
        ∀t : ℕ,6≤ t → t≤ s → ∀center : EuclideanSpace ℝ (Fin 3),
          (((ballEdges D (2^m) p E center (64/((2^t:ℕ):ℝ))).image
            (fun z => angularCell D (2^m) (2^s) p z.1)).card:ℝ)≤
          meshAngularConstant*r^(-loss)*
            ((64/((2^t:ℕ):ℝ))/(64/((2^s:ℕ):ℝ)))^extremalExponent) ∧
    ∀{n g J Jangle : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta eta0 c c2 r : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (htau : 0 < tau) (L : ℕ)
    (ref : Reference h tau htau seed e zeta L g)
    (Hcaller : HasCallerUniformities ref (NativeConditionalReferenceMenu.factory g K))
    (hetaSeed : eta≤ seed/8) (hzeta : 0≤ zeta) (hzseed : zeta≤ seed/256)
    (hSeed : seed≤ seedCap) (hSourceSmall : D.thickness≤ delta0)
    (E2 S I T : Finset (Fin n × Index)) (points : Finset Index) (h21 : E2⊆ref.E1) (hE2n : E2.Nonempty)
    (rank : Fin 4) (hi : 1 ≤ rank.val) (hell : rank.val+1 ≤ 3)
    (heta : 0 ≤ eta) (he0 : 0 < eta0) (hc : 0 < c) (hc1 : c ≤ 1)
    (hcUnit : c ≤ 1/(eta0+1)) (hr : 0 < r) (hr1 : r ≤ 1)
    (hrdelta : r ≤ D.thickness^(cutoff c rank))
    (hmass : r^((2*((rank.val+1:ℕ):ℝ)+1)*rankLoss eta0 c rank)*(E2.card:ℝ) ≤
      (WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ))
    (htauHalf : tau ≤ 1/2) (hTau : tau ≤ commonBudget eta0 c/1024)
    (hTauHistory : tau ≤ commonBudget eta0 c/(1000*((J:ℝ)+1)))
    (hseed : seed ≤ tau/16384) (hc2 : c2=commonBudget eta0 c/4)
    (hg : 0 < g) (hgrid : 1/(g:ℝ) < rankWindow tau/4)
    (F2 G Q2 : ℕ) (hG : 0 < G) (hGF : G ≤ F2)
    (H2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c2))
    (j : Fin (g+1)) (hstop18 : 18 ≤ (ref.schedule j).val)
    (hstopCap : (ref.schedule j).val ≤ ref.level/4)
    (hidentity : 48*((2^(ref.schedule j).val:ℕ):ℝ)*r=1)
    (hpowerMin : amin≤ cutoff c rank) (hdelta : 64*D.thickness≤ r^2)
    (hMiddle : 3072*r≤ ((64:ℝ)/((2^(middleDepth (ref.schedule j).val):ℕ):ℝ))^2)
    (hsmall : D.thickness ≤ NativeHistoryDimensionRange.extraCutoff c hc hc1 g)
    (p : Parent)
    (HS : Saturated (parentEdges D ref.a (2^(middleDepth (ref.schedule j).val)) E2 p) S Prod.snd)
    (HPoint : HasUniformFibers (parentEdges D ref.a (2^(middleDepth (ref.schedule j).val)) E2 p) Q2 Prod.snd)
    (hIS : I⊆ S) (hTI : T⊆ I) (F3 Q3 : ℕ) (hF3 : 0< F3)
    (hret3 : S.card≤ F3*I.card) (HPoint3 : HasUniformFibers I Q3 Prod.snd)
    (hQ3 : 1≤ Q3)
    (H3 : (F3:ℝ)*(Q3:ℝ)^4≤ D.thickness^(-(commonBudget eta0 c/4)))
    (hret :
      let lambda := r^(rankLoss eta0 c rank)/(4*((g:ℝ)+1))
      let W : ℝ := (WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ)
      let mu := (lambda*W/(2*(factor ref.dimension (g+1) L:ℝ)*G*(E2.card:ℝ)))*D.thickness^eta
      (mu/rowConstant)*(parentEdges D ref.a (2^(middleDepth (ref.schedule j).val)) ref.E1 p).card ≤
        (parentEdges D ref.a (2^(middleDepth (ref.schedule j).val)) E2 p).card)
    (s : ℕ) (hs : 6 ≤ s) (hsm : s ≤ middleDepth (ref.schedule j).val+6)
    (sigmaDepth : Fin Jangle → ℕ) (jangle : Fin Jangle)
    (hSigma6 : 6≤ sigmaDepth jangle)
    (hSigmaMax : sigmaDepth jangle≤ middleDepth (ref.schedule j).val+6)
    (k : Index) (hk : k∈I.image Prod.snd) (q : Fin 3 → ℤ)
    (hRich : ((I.filter (fun z => z.2=k)).card:ℝ)/
        (2*(Jangle:ℝ)*(((I.filter (fun z => z.2=k)).image
          (fun z => angularCell D (2^(middleDepth (ref.schedule j).val))
            (2^(sigmaDepth jangle)) p z.1)).card:ℝ)) <
      ((classFiber (T.filter (fun z => z.2=k))
        (fun z => angularCell D (2^(middleDepth (ref.schedule j).val))
          (2^(sigmaDepth jangle)) p z.1) q).card:ℝ)),
    ((64/((2^(sigmaDepth jangle):ℕ):ℝ))/(64/((2^s:ℕ):ℝ)))^extremalExponent≤
      (5488*rowConstant*((g:ℝ)+1)*(Jangle:ℝ)*meshAngularConstant)*
        r^(-(10*rankLoss eta0 c rank+loss))*
        (((classFiber (T.filter (fun z => z.2=k))
          (fun z => angularCell D (2^(middleDepth (ref.schedule j).val))
            (2^(sigmaDepth jangle)) p z.1) q).image
          (fun z => angularCell D (2^(middleDepth (ref.schedule j).val)) (2^s) p z.1)).card:ℝ) := by
  obtain ⟨K,seedCap,delta0,hK,hSeed,hd0,hd08,Hupper⟩ :=
    exists_paid_mesh_angular_bounds amin loss hamin hloss hloss1
  refine ⟨K,seedCap,delta0,hK,hSeed,hd0,hd08,Hupper,?_⟩
  intro n g J Jangle D eta tau seed e zeta eta0 c c2 r h htau L ref Hcaller hetaSeed hzeta hzseed
    hSeed hSourceSmall E2 S I T points h21 hE2n rank hi hell heta he0 hc hc1 hcUnit hr hr1 hrdelta hmass
    htauHalf hTau hTauHistory hseed hc2 hg hgrid F2 G Q2 hG hGF H2 j hstop18 hstopCap hidentity
    hpowerMin hdelta hMiddle hsmall p HS HPoint hIS hTI F3 Q3 hF3 hret3 HPoint3 hQ3 H3 hret
    s hs hsm sigmaDepth jangle hSigma6 hSigmaMax k hk q hRich
  let m : ℕ := middleDepth (ref.schedule j).val
  run_tac Lean.logInfo "paired engines: entered actual source join"
  have hI1 : I⊆ ref.E1 := hIS.trans (HS.1.trans ((filter_subset _ _).trans h21))
  have hLower := actual_all_mesh_rich_class_lower (D := D) (n := n) (g := g) (J := J) (Jangle := Jangle) h htau L ref E2 S I T points h21 hE2n rank hi hell
    heta he0 hc hc1 hcUnit hr hr1 hrdelta hmass htauHalf hTau hTauHistory hseed hc2 hg hgrid F2 G Q2
    hG hGF H2 j hstop18 hstopCap hidentity hsmall p HS HPoint hIS hTI F3 Q3 hF3 hret3 HPoint3 hret
    s hs hsm sigmaDepth jangle k hk q hRich
  run_tac Lean.logInfo "paired engines: source lower read"
  let Ik : Finset (Fin n × Index) := I.filter (fun z => z.2=k)
  have hIkParent : ∀z∈Ik,parentLabel D ref.a (2^m) z.1=p := by
    intro z hz
    exact (mem_filter.mp (HS.1 (hIS (mem_filter.mp hz).1))).2
  have hUpper := (Hupper n D eta zeta seed tau e h htau L g heta hzeta hetaSeed hzseed hSeed hSourceSmall
    ref Hcaller j (by omega) (sigmaDepth jangle) hSigma6 hSigmaMax r (cutoff c rank) hr hrdelta
    hpowerMin hdelta hMiddle p Ik ((filter_subset _ _).trans hI1) hIkParent
    (physicalCell D ref.a (2^m) (2^(sigmaDepth jangle)) p k)
    (fun z hz => by rw [(mem_filter.mp hz).2])).1
  run_tac Lean.logInfo "paired engines: source upper read"
  have hThird := third_cost (delta := D.thickness) (r := r) (power := cutoff c rank)
    (rankLoss := rankLoss eta0 c rank) h.1.2.1 hr (cutoff_bounds hc hc1 rank).1 (rankLoss_pos he0 hc rank).le hrdelta
    F3 Q3 hQ3 (by rw [cutoff_mul_rankLoss eta0 c rank]; exact H3)
  run_tac Lean.logInfo "paired engines: third cost paid"
  let Nsig : ℝ := (Ik.image (fun z => angularCell D (2^m) (2^(sigmaDepth jangle)) p z.1)).card
  let Nfine : ℝ := (((classFiber (T.filter (fun z => z.2=k))
    (fun z => angularCell D (2^m) (2^(sigmaDepth jangle)) p z.1) q).image
      (fun z => angularCell D (2^m) (2^s) p z.1)).card:ℝ)
  have hLowerRead : (64/((2^s:ℕ):ℝ))^(-extremalExponent)≤
      (2744*rowConstant*((g:ℝ)+1))*r^(-(9*rankLoss eta0 c rank))*
        ((F3:ℝ)*(Q3:ℝ)^2)*(2*(Jangle:ℝ)*Nsig)*Nfine := by
    simpa only [m,Ik,Nfine,Nsig,mul_assoc] using hLower
  run_tac Lean.logInfo "paired engines: lower scalar readback aligned"
  have hUpperRead : Nsig≤ meshAngularConstant*r^(-loss)*(64/((2^(sigmaDepth jangle):ℕ):ℝ))^(-extremalExponent) := hUpper
  have hFinal := cancel_rich_class (kappa := extremalExponent)
    (rankLoss := rankLoss eta0 c rank) (loss := loss) (Nfine := Nfine) (Nsig := Nsig)
    (C := 2744*rowConstant*((g:ℝ)+1)) (U := meshAngularConstant) (J := (Jangle:ℝ))
    (P := (F3:ℝ)*(Q3:ℝ)^2) hr hr1
    (by positivity : 0< (64:ℝ)/((2^s:ℕ):ℝ))
    (by positivity : 0< (64:ℝ)/((2^(sigmaDepth jangle):ℕ):ℝ))
    (rankLoss_pos he0 hc rank).le
    (show 0≤ 2744*rowConstant*((g:ℝ)+1) by have hh := rowConstant_pos; positivity)
    (show 0≤ meshAngularConstant by dsimp [meshAngularConstant,NativeSameSourceConditionalAngularUpper.conditionalConstant]; positivity)
    (Nat.cast_nonneg Jangle) (show 0≤ (F3:ℝ)*(Q3:ℝ)^2 by positivity)
    (show 0≤ Nsig from Nat.cast_nonneg _)
    (show 0≤ Nfine from Nat.cast_nonneg _)
    hLowerRead hUpperRead hThird
  run_tac Lean.logInfo "paired engines: finite payment complete"
  rw [rich_coefficient g Jangle] at hFinal
  simpa only [Nfine,m] using hFinal

end NativePairedAngularEngines
