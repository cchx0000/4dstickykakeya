import Theorems.Thm_StickyKakeya4_native_conditional_angular_scale_readback

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 11000000

noncomputable section
namespace NativeSameSourceConditionalAngularUpper
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeMiddleWindowBalance NativeReferenceParentCompleteAngularUpper NativeRelativeCoarseReadback
open NativeJointUniformCoarseRelations NativeNormalizedCellAngularMenu NativeNormalizedCellRelativeMenu
open NativeFixedCompactKakeyaExponent NativeReferenceXYGridAngularCap
open NativeConditionalAngularCountTransfer NativeConditionalAngularScaleReadback

def conditionalConstant : ℝ := (2049:ℝ)^3*7^4*512

/-- Same-source two-scale angular upper. One actual outer rho-cell and
one standard sigma angular cell are counted using the original full
sigma-phase parents and their admitted E1 relative sources. Both relative
window endpoints are derived or paid; no common direction-AD input occurs.
The three equality slots are installed before E1, as in ReferenceRelativeMenu. -/
theorem exists_conditional_angular_upper (epsilon window budget : ℝ)
    (hepsilon : 0< epsilon) (hwindow : 0< window) (hbudget : 0< budget)
    (hWindowBudget : 3*window≤ budget) :
    ∃seedCap delta0 : ℝ,0< seedCap ∧ 0< delta0 ∧ delta0≤ 1/8 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta zeta seed a : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        0≤ zeta → eta≤ seed/8 → zeta≤ seed/256 → seed≤ seedCap → D.thickness≤ delta0 →
      ∀(original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ),
        HasOriginalBackbone D original R a level zeta →
      ∀E1 : Finset (Fin n × Index),E1⊆ retained original R →
      ∀(F Q m s t : ℕ) (r power : ℝ),1≤ Q → 6≤ t → t≤ s → s≤ m → m+s-6≤ level →
        0< r → r≤ D.thickness^power → window≤ power →
        64*D.thickness≤ r^2 → 3072*r≤ ((64:ℝ)/((2^m:ℕ):ℝ))^2 →
        (incidences original).card≤ F*E1.card →
        (∀x y,x∈E1 → y∈E1 →
          (parentEdges D a (2^(m+t-6)) E1 (parentLabel D a (2^(m+t-6)) x.1)).card≤ 
            Q^2*(parentEdges D a (2^(m+t-6)) E1 (parentLabel D a (2^(m+t-6)) y.1)).card) →
        (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*D.thickness^(-eta)≤ D.thickness^(-(seed/8)) →
        (∀q : Parent,∀hq : (parentLabels D R a (2^(m+t-6)) q).Nonempty,
          HasUniformFibers (parentEdges D a (2^(m+t-6)) E1 q) Q
            (doublePair h R a (m+t-6) q hq (2^(s-t+6))) ∧
          HasUniformFibers (parentEdges D a (2^(m+t-6)) E1 q) Q
            (fun z => (doublePair h R a (m+t-6) q hq (2^(s-t+6)) z).2)) →
      ∀(p : Parent) (E : Finset (Fin n × Index)),E⊆ E1 →
        (∀z∈E,parentLabel D a (2^m) z.1=p) →
      ∀(cell : Index) (angle : Fin 3 → ℤ),
        (∀z∈E,physicalCell D a (2^m) (2^s) p z.2=cell) →
        (∀z∈E,localAngle D (2^m) p (64/((2^t:ℕ):ℝ)) z.1=angle) →
        ((E.image (fun z => angularCell D (2^m) (2^s) p z.1)).card:ℝ)≤ 
          conditionalConstant*(Q:ℝ)^4*(((2^(m+t-6):ℕ):ℝ)*D.thickness/64)^(-budget)*
            ((64/((2^s:ℕ):ℝ))/(64/((2^t:ℕ):ℝ)))^(-extremalExponent-epsilon) := by
  obtain ⟨localEta,seedCap,delta0,_hLocal,hSeed,hd0,hd08,Hengine⟩ :=
    exists_reference_parent_upper epsilon window budget hepsilon hwindow hbudget hWindowBudget
  refine ⟨seedCap,delta0,hSeed,hd0,hd08,?_⟩
  intro n D eta zeta seed a h hzeta heta hzseed hseed hsmall original R level HB E1 hE1
    F Q m s t r power hQ ht hts hsm hlevel hr hrscale hwa hdelta hMiddle hret Hparent Hcost Hrelative
    p E hEE1 hParent cell angle hCell hAngle
  obtain ⟨hbL,hu6,huL,hSquare,hFine⟩ := actual_nested_scale_budgets h.1.2.1 h.1.2.2.1 hr hrscale
    hwindow.le hwa m s t level ht hts hsm hlevel hdelta hMiddle
  let B : ℝ := 512*(Q:ℝ)^4*(((2^(m+t-6):ℕ):ℝ)*D.thickness/64)^(-budget)*
    (64/((2^(s-t+6):ℕ):ℝ))^(-extremalExponent-epsilon)
  have hB : 0≤ B := by dsimp [B]; have hd := h.1.2.1; positivity
  have hConditional := conditional_angular_count h original HB.1 HB.2.2.1 level m s t HB.2.1 ht hts hlevel
    p E E1 (hE1.trans (filter_subset _ _)) hEE1 hParent cell angle hCell hAngle B hB (by
      intro q hq v
      obtain ⟨z,hz,hzq⟩ := mem_image.mp hq
      have hzRef : z∈parentEdges D a (2^(m+t-6)) E1 q := mem_filter.mpr ⟨hEE1 hz,hzq⟩
      have hpRef : (parentEdges D a (2^(m+t-6)) E1 q).Nonempty := ⟨z,hzRef⟩
      have hpR : (parentLabels D R a (2^(m+t-6)) q).Nonempty := by
        refine ⟨z.1,mem_filter.mpr ⟨?_,hzq⟩⟩
        exact (mem_filter.mp (hE1 (hEE1 hz))).2
      obtain ⟨_hNative,_hCompact,Hupper⟩ := Hengine n D eta zeta seed a h hzeta heta hzseed hseed hsmall
        original R level HB E1 hE1 F Q (m+t-6) hQ hbL hSquare hret Hparent Hcost q hpRef
      exact Hupper hpR (s-t+6) hu6 huL hFine (Hrelative q hpR).1 (Hrelative q hpR).2
        _ (Subset.refl _) v)
  dsimp only [B] at hConditional
  rw [relative_width_ratio s t ht hts] at hConditional
  simpa only [conditionalConstant,mul_assoc,mul_comm,mul_left_comm] using hConditional

end NativeSameSourceConditionalAngularUpper
