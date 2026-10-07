import Theorems.Thm_StickyKakeya4_native_parent_unit_angular_ball

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

noncomputable section
namespace NativePaidMeshAngularBounds
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeLocalParentSource NativeRelativeCoarseReadback
open NativeGenericReferenceData NativeExtraQueriedRankConfiguration NativeConditionalReferenceMenu
open NativeSameSourceConditionalAngularUpper NativeSameSourceAngularBallUpper
open NativeLocalParentGeometry NativeNormalizedCellRelativeMenu NativeNormalizedCellAngularMenu
open NativeFixedCompactKakeyaExponent NativeMiddleGrainParentBudget

open NativeConditionalReferenceAngularUpper NativeConditionalGridCoverage
open NativeConditionalGridPowerCost NativeAngularDyadicInterpolation

open NativeAllDyadicReferenceAngularUpper NativeAngularBottomEndpoint NativeConditionalUpperParameters

open NativePaidMeshAngularUpper NativeParentUnitAngularBall

def ballEdges {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (p : Parent)
    (E : Finset (Fin n × Index)) (center : EuclideanSpace ℝ (Fin 3)) (sigma : ℝ) :=
  E.filter (fun z => dist (localSlope D N p z.1) center≤ sigma)

/-- One actual Reference and one fixed pre-source menu simultaneously give
the full angular union and every genuine two-scale angular-ball upper on
that same union, through the final mesh Rho/64. -/
theorem exists_paid_mesh_angular_bounds (amin loss : ℝ)
    (hamin : 0< amin) (hloss : 0< loss) (hloss1 : loss≤ 1) :
    ∃(K : ℕ) (seedCap delta0 : ℝ),0< K ∧ 0< seedCap ∧ 0< delta0 ∧ delta0≤ 1/8 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta zeta seed tau e : ℝ)
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
            ((64/((2^t:ℕ):ℝ))/(64/((2^s:ℕ):ℝ)))^extremalExponent := by
  obtain ⟨K,seedCap,delta0,hK,hSeed,hd0,hd08,Hupper⟩ :=
    exists_paid_mesh_angular_ball_upper amin loss hamin hloss hloss1
  refine ⟨K,seedCap,delta0,hK,hSeed,hd0,hd08,?_⟩
  intro n D eta zeta seed tau e h htau L g heta hzeta hetaSeed hzseed hseed hsmall
    ref Hcaller i hstop m s hs hsm r power hr hrscale hpower hdelta hMiddle
    p E hE hParent cell hCell
  constructor
  · have hBall : ∀z∈E,dist (localSlope D (2^m) p z.1) NativeParentUnitAngularBall.center≤
        64/((2^6:ℕ):ℝ) := by
      intro z hz
      simpa using localSlope_in_unit_ball D ref.a (2^m) p z.1 (hParent z hz)
    have hh := Hupper n D eta zeta seed tau e h htau L g heta hzeta hetaSeed hzseed hseed hsmall
      ref Hcaller i hstop s 6 (by norm_num) hs hsm r power hr hrscale hpower hdelta hMiddle
      p E hE hParent cell NativeParentUnitAngularBall.center hCell hBall
    have hid : ((64/((2^6:ℕ):ℝ))/(64/((2^s:ℕ):ℝ)))^extremalExponent=
        (64/((2^s:ℕ):ℝ))^(-extremalExponent) := by
      norm_num only [show (2:ℕ)^6=64 by norm_num,Nat.cast_ofNat,div_self (by norm_num : (64:ℝ)≠0),one_div]
      rw [Real.inv_rpow (by positivity),Real.rpow_neg (by positivity)]
    rwa [hid] at hh
  · intro t ht hts center
    exact Hupper n D eta zeta seed tau e h htau L g heta hzeta hetaSeed hzseed hseed hsmall
      ref Hcaller i hstop s t ht hts hsm r power hr hrscale hpower hdelta hMiddle
      p (ballEdges D (2^m) p E center (64/((2^t:ℕ):ℝ)))
      ((filter_subset _ _).trans hE) (fun z hz => hParent z (mem_filter.mp hz).1)
      cell center (fun z hz => hCell z (mem_filter.mp hz).1) (fun _ hz => (mem_filter.mp hz).2)

end NativePaidMeshAngularBounds
