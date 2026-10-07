import Theorems.Thm_StickyKakeya4_native_local_pair_uniform_core
import Theorems.Thm_StickyKakeya4_native_conditional_coarse_interpolation
import Theorems.Thm_StickyKakeya4_native_same_source_multiplicity_balance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

noncomputable section
namespace NativeRankRefinedReferenceCore
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalParentDensityCore NativeCubicalIncidenceCounts NativeLocalPairUniformCore
open NativeLocalPairFibers NativeJointUniformCoarseRelations NativeIncidenceMultiplicityTower
open NativeConditionalCoarseInterpolation NativeCoarseFineMultiplicity SelfUniform

/-- Refine an actual rank-selected subset inside a fixed original reference.
The original native D remains the upper reference. The new incidence set is
not claimed to be a small-exponent native source. Its rank-retention cost
appears only in the proved lower/richness budgets; image uppers cost radRef^4. -/
theorem exists_refined_reference_core {n : ℕ} {D : FiniteScaleSource n}
    {eta a : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈
      Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) (hsmall : D.thickness ≤ 1/8)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index))
    (hE1 : E1 ⊆ retained original R) (hE1ne : E1.Nonempty) (hF : F ⊆ E1)
    (F1 : ℕ) (hF1 : 0 < F1)
    (hret1 : (incidences original).card ≤ F1*E1.card)
    (lambda : ℝ) (hlambda : 0 < lambda) (hrank : lambda*(E1.card:ℝ) ≤ F.card)
    (d g L : ℕ) (hdg : 0 < d+g) (hL : 0 < L)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (hrefl : ∀j x,Rel j x x) (hsym : ∀j x y,Rel j x y → Rel j y x)
    (scales : Fin g → ℕ) (hN : ∀j,0 < scales j)
    (hscale : ∀j,(scales j:ℝ)*D.thickness/64 ≤ 1)
    (t radRef : ℕ) (maps : Fin t → (Fin n × Index) → Parent × Index)
    (hpair : ∀j,HasUniformFibers E1 radRef (maps j))
    (hpoint : ∀j,HasUniformFibers E1 radRef (fun z => (maps j z).2)) :
    let Q := NativeSourceSizeBounds.radix F.card L
    let G := retentionCost d g L
    ∃ E2 ⊆ F, E2.Nonempty ∧ E2 ⊆ retained original R ∧
      F.card ≤ G*E2.card ∧
      lambda/((F1:ℝ)*G)*multiplicity (incidences original) ≤ multiplicity E2 ∧
      (∀j x y,x∈E2 → y∈E2 →
        degree (fun _ : Fin n × Index => 1) (Rel j) E2 x ≤
          Q^2*degree (fun _ : Fin n × Index => 1) (Rel j) E2 y) ∧
      (∀j e,e∈E2 → D.thickness^eta*scales j/
        (16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q:ℝ)^2) ≤
          (pairFiber D a (scales j) E2 (localPair D a (scales j) e)).card) ∧
      ∀j,multiplicity (E2.image (maps j)) ≤
        (radRef:ℝ)^4*multiplicity (E1.image (maps j)) := by
  let G := retentionCost d g L
  have hI : retained original R ⊆ incidences original := filter_subset _ _
  have hForig : F ⊆ incidences original := hF.trans (hE1.trans hI)
  have hFne : F.Nonempty := by
    apply card_pos.mp
    have hp : (0:ℝ) < E1.card := by exact_mod_cast card_pos.mpr hE1ne
    have hh : (0:ℝ) < F.card := (mul_pos hlambda hp).trans_le hrank
    exact_mod_cast hh
  have hF1r : (0:ℝ) < F1 := by exact_mod_cast hF1
  have hF0 : 0 < (F1:ℝ)/lambda := div_pos hF1r hlambda
  have hsource : ((incidences original).card:ℝ) ≤ ((F1:ℝ)/lambda)*F.card := by
    have hretR : ((incidences original).card:ℝ) ≤ (F1:ℝ)*E1.card := by exact_mod_cast hret1
    have he1 : (E1.card:ℝ) ≤ (F.card:ℝ)/lambda := (le_div_iff₀ hlambda).mpr
      (by simpa only [mul_comm] using hrank)
    exact hretR.trans ((mul_le_mul_of_nonneg_left he1 hF1r.le).trans_eq (by ring))
  obtain ⟨E2,hE2F,hE2ne,hret2,hUniform,hRich⟩ :=
    exists_retained_scheduled_pair_core h original horiginal ha hsmall F hForig hFne
      hF0 hsource d g L hdg hL Rel hrefl hsym scales hN hscale
  have hG : (0:ℝ) < G := by dsimp [G,retentionCost]; positivity
  have hret2R : (F.card:ℝ) ≤ (G:ℝ)*E2.card := by exact_mod_cast hret2
  have hcard : lambda/((F1:ℝ)*G)*((incidences original).card:ℝ) ≤ E2.card := by
    have hh := hsource.trans (mul_le_mul_of_nonneg_left hret2R hF0.le)
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (mul_pos hF1r hG)).mpr
    have hmul := mul_le_mul_of_nonneg_left hh hlambda.le
    have he : lambda*((F1:ℝ)/lambda*((G:ℝ)*E2.card)) =
        (E2.card:ℝ)*((F1:ℝ)*G) := by field_simp
    rw [he] at hmul
    exact hmul
  have hE2I : E2 ⊆ incidences original := hE2F.trans hForig
  have hnear := retained_incidence_multiplicity (incidences original) E2 hE2I
    (show 0 ≤ lambda/((F1:ℝ)*G) by positivity) hcard
  refine ⟨E2,hE2F,hE2ne,hE2F.trans (hF.trans hE1),hret2,hnear,hUniform,hRich,?_⟩
  intro j
  exact subset_image_multiplicity E1 E2 (hE2F.trans hF) (maps j) radRef (hpair j) (hpoint j)

end NativeRankRefinedReferenceCore
