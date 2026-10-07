import Theorems.Thm_StickyKakeya4_native_parent_angular_coarse_endpoint

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8500000

noncomputable section
namespace NativeReferenceParentCompleteAngularUpper
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeMiddleWindowBalance NativeReferenceParentAngularUpper NativeParentAngularCoarseEndpoint
open NativeUnitParentNormalization NativeRelativeCoarseReadback NativeJointUniformCoarseRelations
open NativeNormalizedCellAngularMenu NativeFixedCompactKakeyaExponent

/-- The full coarse end of the angular range follows from the actual
parent slope box. The native relative engine is used only inside its
proved window. The fine endpoint remains explicit for its source readback. -/
theorem exists_reference_parent_upper (epsilon window budget : ℝ)
    (hepsilon : 0< epsilon) (hwindow : 0< window) (hbudget : 0< budget)
    (hWindowBudget : 3*window≤ budget) :
    ∃localEta seedCap delta0 : ℝ,
      0< localEta ∧ 0< seedCap ∧ 0< delta0 ∧ delta0≤ 1/8 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta zeta seed a : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        0≤ zeta → eta≤ seed/8 → zeta≤ seed/256 → seed≤ seedCap → D.thickness≤ delta0 →
      ∀(original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ),
        HasOriginalBackbone D original R a level zeta →
      ∀E1 : Finset (Fin n × Index),E1⊆ retained original R →
      ∀F Q m : ℕ,1≤ Q → m≤ level → D.thickness≤ (64/((2^m:ℕ):ℝ))^2 →
        (incidences original).card≤ F*E1.card →
        (∀x y,x∈E1 → y∈E1 →
          (parentEdges D a (2^m) E1 (parentLabel D a (2^m) x.1)).card≤ 
            Q^2*(parentEdges D a (2^m) E1 (parentLabel D a (2^m) y.1)).card) →
        (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*D.thickness^(-eta)≤ D.thickness^(-(seed/8)) →
      ∀p : Parent,(parentEdges D a (2^m) E1 p).Nonempty →
        let E := parentEdges D a (2^m) E1 p
        IsWangZakharovNativeFiniteInput (source h R E a m p) localEta ∧
        (∀i,(source h R E a m p).line i∈fixedCompactClass) ∧
        ∀hp : (parentLabels D R a (2^m) p).Nonempty,
        ∀s : ℕ,6≤ s → s≤ level-m+6 →
          (source h R E a m p).thickness/(1/((2^s:ℕ):ℝ))≤ (source h R E a m p).thickness^window →
          HasUniformFibers E Q (doublePair h R a m p hp (2^s)) →
          HasUniformFibers E Q (fun z => (doublePair h R a m p hp (2^s) z).2) →
        ∀T⊆ E,∀q : Index,((angularMenu D a m (2^s) p T q).card:ℝ)≤ 
          512*(Q:ℝ)^4*(source h R E a m p).thickness^(-budget)*
            (64/((2^s:ℕ):ℝ))^(-extremalExponent-epsilon) := by
  obtain ⟨e,localEta,seedCap,delta0,_he,_heBound,hLocal,hSeed,hd0,hd08,Hengine⟩ :=
    exists_reference_parent_angular_upper epsilon window budget hepsilon hwindow hbudget
  refine ⟨localEta,seedCap,delta0,hLocal,hSeed,hd0,hd08,?_⟩
  intro n D eta zeta seed a h hzeta heta hzseed hseed hsmall original R level HB E1 hE1 F Q m hQ hm
    hsquare hret Hparent Hcost p hp
  obtain ⟨hS,hSK,Hupper⟩ := Hengine n D eta zeta seed a h hzeta heta hzseed hseed hsmall original R level
    HB E1 hE1 F Q m hm hsquare hret Hparent Hcost p hp
  refine ⟨hS,hSK,?_⟩
  intro hpR s hs6 hs hfine hPair hPoint T hTE q
  have hQ4 : (1:ℝ)≤ (Q:ℝ)^4 := one_le_pow₀ (by exact_mod_cast hQ)
  have hLocalPos := hS.1.2.1
  have hLocalOne := hS.1.2.2.1
  by_cases hcoarse : 1/((2^s:ℕ):ℝ)≤ (source h R (parentEdges D a (2^m) E1 p) a m p).thickness^window
  · have hh := Hupper hpR s hs hcoarse hfine hPair hPoint T hTE q
    apply hh.trans
    have hP0 : 0≤ (source h R (parentEdges D a (2^m) E1 p) a m p).thickness^(-budget) :=
      Real.rpow_nonneg hLocalPos.le _
    have hR0 : 0≤ (64/((2^s:ℕ):ℝ))^(-extremalExponent-epsilon) := by positivity
    gcongr
    norm_num
  · have hAmbient := angular_menu_box D a m s (by omega) p T
      (fun z hz => (mem_filter.mp (hTE hz)).2) q
    have hh := coarse_endpoint_cost hLocalPos hLocalOne extremalExponent_nonneg hepsilon.le
      hWindowBudget s hs6 hcoarse hAmbient
    apply hh.trans
    have hCoeff : (512:ℝ)≤ 512*(Q:ℝ)^4 := by nlinarith only [hQ4]
    have hP0 : 0≤ (source h R (parentEdges D a (2^m) E1 p) a m p).thickness^(-budget) :=
      Real.rpow_nonneg hLocalPos.le _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCoeff hP0) (by positivity)

end NativeReferenceParentCompleteAngularUpper
