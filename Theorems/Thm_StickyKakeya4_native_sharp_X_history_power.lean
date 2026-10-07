import Theorems.Thm_StickyKakeya4_native_sharp_X_power_algebra
import Theorems.Thm_StickyKakeya4_native_history_grain_power_density
import Theorems.Thm_StickyKakeya4_native_anisotropic_column_capacity

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeSharpXHistoryPower
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeJointUniformCoarseRelations
open NativeSpatialAngularGeometry NativeSquaredGrainQueries NativeActualProjectedGrainCount
open NativeQueriedVertexWeights NativeOriginalPacketReference NativeCompatibleNodeDirections
open NativeActualGrainHistory NativeHistoryGrainPowerDensity NativeActualRichPacketLayers
open NativeParentGrainIncidenceCleanup NativeSourceParentGrainCleanup
open NativeSharpXPowerAlgebra NativeRetainedSliceBudgetAlgebra
open RichDirectionalLayers WeightedRichDirectionalLayers

lemma actual_time_count (m : ℕ) (hm6 : 6 ≤ m) :
    (((2^(phaseDepth m-m):ℕ):ℝ))=1/((64:ℝ)/((2^m:ℕ):ℝ)) := by
  have hm : m ≤ phaseDepth m := by dsimp [phaseDepth]; omega
  calc
    _ = ((64:ℝ)/((2^m:ℕ):ℝ))/((64:ℝ)/((2^(phaseDepth m):ℕ):ℝ)) :=
      (eq_div_iff (by positivity)).mpr (NativeAnisotropicColumnCapacity.dyadic_height_eq m (phaseDepth m) hm).symm
    _ = _ := short_fine_scale_ratio m hm6

/-- Read the actual history gain and squared-scale time count into the
ell-1 power, keeping precisely the original final point weight fraction. -/
theorem history_power_to_X {n J : ℕ} {D : FiniteScaleSource n} {eta lambda q c1 c2 : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (E : Finset (Fin n × Index)) (hE : E.Nonempty)
    (m : Fin J → ℕ) (ell : ℕ) (hell : 1 ≤ ell) (S0 : Finset Index) (hS0 : S0⊆E.image Prod.snd)
    (dir : Fin J → ℕ → Index → Fin n) (Q2 : ℕ)
    (HU : ∀i,HasUniformFibers E Q2 (fun z => spatialLabel D (2^(phaseDepth (m i))) z.2))
    (Hhistory : HasGrainHistory D E m ell dir S0 Q2 lambda c1 c2)
    (i : Fin J) (hm6 : 6 ≤ m i) (K : Finset Index)
    (hK : K⊆history D E m ell dir S0 J) (hKn : K.Nonempty)
    (hlambda : 0 < lambda) (F1 G F3 Q3 : ℕ) (zeta tau X : ℝ)
    (Hcross : lambda*D.thickness^(2*eta+3*zeta+7*tau)*(mass K (pointWeight E):ℝ)*
      (predecessorProduct D (m i) E Q2
        (scaleThreshold D E (m i) (history D E m ell dir S0 i.val) ell (dir i)) ell:ℝ) ≤
      parentGrainConstant*transverseCost q ell*(Q2:ℝ)^2*(F1:ℝ)*G*E.card*
        (quotientCost q*(F3:ℝ)*(Q3:ℝ)^2)*(((2^(phaseDepth (m i)-m i):ℕ):ℝ))*X) :
    ((64:ℝ)/((2^(m i):ℕ):ℝ))^(-((ell:ℝ)-1)) ≤
      fiberCoefficient D.thickness eta zeta tau c1 c2 lambda
        ((mass K (pointWeight E):ℝ)/(E.card:ℝ)) F1 G Q2 F3 Q3 q ell*X := by
  let N : ℝ := E.card
  let W : ℝ := mass K (pointWeight E)
  let b := W/N
  let rho := (64:ℝ)/((2^(m i):ℕ):ℝ)
  let C := 2*(ell:ℝ)*(referenceConstant:ℝ)
  let current := history D E m ell dir S0 i.val
  let Lgrain := predecessorProduct D (m i) E Q2 (scaleThreshold D E (m i) current ell (dir i)) ell
  let Dcost := parentGrainConstant*transverseCost q ell*(Q2:ℝ)^2*(F1:ℝ)*G*
    (quotientCost q*(F3:ℝ)*(Q3:ℝ)^2)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast card_pos.mpr hE
  have hKpoint : K⊆E.image Prod.snd := hK.trans ((Hhistory.2.2.1 J le_rfl).2.1.trans hS0)
  have hW : 0 < W := by
    have hcut : (cutEdges E K).Nonempty := by
      have hh : ((cutEdges E K).image Prod.snd).Nonempty := by rwa [cutEdges_points E K hKpoint]
      exact hh.of_image
    dsimp [W]
    rw [←cutEdges_card E K]
    exact_mod_cast card_pos.mpr hcut
  have hb : 0 < b := div_pos hW hN
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hC : 0 < C := by
    have hellr : (0:ℝ)<ell := by exact_mod_cast hell
    have href := referenceConstant_pos
    dsimp [C]
    positivity
  have hd := h.1.2.1
  have hKcurrent : K⊆current := hK.trans (history_antitone D E m ell dir S0 (Nat.le_of_lt i.isLt))
  have hmass : W ≤ (mass current (pointWeight E):ℝ) := by
    dsimp [W]
    exact_mod_cast WeightedRichDirectionalLayers.mass_mono K current (pointWeight E) hKcurrent
  have hgain : (b*lambda*D.thickness^(c1+5*c2)/(C*rho))^ell ≤ (Lgrain:ℝ) := by
    have hbase : b*lambda*D.thickness^(c1+5*c2)/(C*rho) ≤ scaleGain D E (m i) current ell lambda c1 c2 := by
      dsimp [b,scaleGain,C,rho,N]
      gcongr
    exact (pow_le_pow_left₀ (by positivity) hbase ell).trans
      (scale_predecessor_power_lower D E hE (m i) current ell (dir i) Q2 lambda c1 c2
        hd hlambda.le (HU i) (Hhistory.2.2.2.2.1 i))
  have hnormalized : lambda*D.thickness^(2*eta+3*zeta+7*tau)*b*
      (b*lambda*D.thickness^(c1+5*c2)/(C*rho))^ell ≤ Dcost*(1/rho)*X := by
    apply (mul_le_mul_iff_right₀ hN).mp
    calc
      _ = lambda*D.thickness^(2*eta+3*zeta+7*tau)*W*
          (b*lambda*D.thickness^(c1+5*c2)/(C*rho))^ell := by dsimp [b]; field_simp
      _ ≤ lambda*D.thickness^(2*eta+3*zeta+7*tau)*W*(Lgrain:ℝ) :=
        mul_le_mul_of_nonneg_left hgain (by positivity)
      _ ≤ N*(Dcost*(1/rho)*X) := by
        have hh := Hcross
        rw [actual_time_count (m i) hm6] at hh
        convert hh using 1
        dsimp [Dcost,N,W,Lgrain,current,rho]
        ring
  have hh := gain_to_X ell hd hrho hC hlambda hb hnormalized
  convert hh using 1
  dsimp [fiberCoefficient,Dcost,C,b,N,W,rho]
  ring

end NativeSharpXHistoryPower
