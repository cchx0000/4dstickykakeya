import Theorems.Thm_StickyKakeya4_native_coarse_shading_capacity
import Theorems.Thm_StickyKakeya4_native_dense_retained_unit_parent
import Theorems.Thm_StickyKakeya4_native_incidence_multiplicity_tower
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section
namespace NativeCoarseFineMultiplicity
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCoarseShadingCapacity NativeCubicalIncidenceCounts NativeIncidenceMultiplicityTower
open NativeDenseRetainedUnitParent NativeOriginalPrunedMass
open scoped BigOperators ENNReal

/-- Multiplicity increases by at least the actual retained incidence fraction:
the retained support is a subset of the original support. No unrestricted
average-multiplicity monotonicity is asserted. -/
lemma retained_incidence_multiplicity {T X : Type*} [DecidableEq X]
    (I J : Finset (T×X)) (hJI : J⊆I) {gamma : ℝ} (hg : 0 ≤ gamma)
    (hret : gamma*(I.card:ℝ) ≤ J.card) :
    gamma*NativeIncidenceMultiplicityTower.multiplicity I ≤ NativeIncidenceMultiplicityTower.multiplicity J := by
  by_cases hJ : J.Nonempty
  · have hp : (0:ℝ)<(J.image Prod.snd).card := by exact_mod_cast card_pos.mpr (hJ.image Prod.snd)
    have hs : ((J.image Prod.snd).card:ℝ) ≤ (I.image Prod.snd).card := by
      exact_mod_cast card_le_card (image_subset_image hJI)
    calc
      _ = (gamma*(I.card:ℝ))/(I.image Prod.snd).card := by
        dsimp [NativeIncidenceMultiplicityTower.multiplicity]
        ring
      _ ≤ (gamma*(I.card:ℝ))/(J.image Prod.snd).card :=
        div_le_div_of_nonneg_left (mul_nonneg hg (Nat.cast_nonneg _)) hp hs
      _ ≤ (J.card:ℝ)/(J.image Prod.snd).card := div_le_div_of_nonneg_right hret hp.le
      _ = _ := rfl
  · have he : J=∅ := not_nonempty_iff_eq_empty.mp hJ
    have hz : gamma*(I.card:ℝ)=0 := le_antisymm (by simpa only [he,card_empty,Nat.cast_zero] using hret)
      (mul_nonneg hg (Nat.cast_nonneg _))
    simp only [NativeIncidenceMultiplicityTower.multiplicity,he,card_empty,image_empty,Nat.cast_zero,div_zero]
    rw [←mul_div_assoc,hz,zero_div]

/-- Original cubical volume retention is exactly original finite incidence
retention, because all those original shadings keep the same delta/2 mesh. -/
theorem original_fine_card_retention {n : ℕ} {D : FiniteScaleSource n} {eta zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i) (F : Finset (Fin n))
    (hmass : (wzTotalShadingVolume D).toReal ≤ D.thickness^(-zeta)*realShadingMass D F) :
    D.thickness^zeta*((incidences original).card:ℝ) ≤ (retained original F).card := by
  have hd := h.1.2.1
  have ho : (wzTotalShadingVolume D).toReal=((incidences original).card:ℝ)*(D.thickness/2)^4 := by
    rw [total_shading_eq_incidence_volume D (half_pos hd) original horiginal]
    simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (half_pos hd).le]
  have hf : realShadingMass D F=((retained original F).card:ℝ)*(D.thickness/2)^4 :=
    retained_shading_real hd original horiginal F
  rw [ho,hf] at hmass
  have hh := mul_le_mul_of_nonneg_left hmass (Real.rpow_pos_of_pos hd zeta).le
  have he : D.thickness^zeta*(D.thickness^(-zeta)*(((retained original F).card:ℝ)*(D.thickness/2)^4))=
      ((retained original F).card:ℝ)*(D.thickness/2)^4 := by
    rw [←mul_assoc,←Real.rpow_add hd]
    simp
  rw [he] at hh
  apply (mul_le_mul_iff_left₀ (show 0 < (D.thickness/2)^4 by positivity)).mp
  simpa only [mul_assoc] using hh

/-- This is the SAME original fine family selected by whole coarse parents.
Its actual measure multiplicity loses only the proved fine shading fraction. -/
theorem original_fine_multiplicity_retention {n : ℕ} {D : FiniteScaleSource n} {eta zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i) (F : Finset (Fin n))
    (hmass : (wzTotalShadingVolume D).toReal ≤ D.thickness^(-zeta)*realShadingMass D F) :
    D.thickness^zeta*(NativeFiniteKakeyaCounts.multiplicity D).toReal ≤
      NativeIncidenceMultiplicityTower.multiplicity (retained original F) := by
  rw [source_multiplicity_real h original horiginal]
  exact retained_incidence_multiplicity (incidences original) (retained original F)
    (filter_subset _ _) (Real.rpow_pos_of_pos h.1.2.1 _).le
    (original_fine_card_retention h original horiginal F hmass)

/-- The actual near-extremal lower power is preserved on those original fine
incidences with its explicit selection loss, ready for the multiplicity tower. -/
theorem retained_original_near_multiplicity {n : ℕ} {D : FiniteScaleSource n} {eta zeta kappa theta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i) (F : Finset (Fin n))
    (hmass : (wzTotalShadingVolume D).toReal ≤ D.thickness^(-zeta)*realShadingMass D F)
    (hnear : D.thickness^(-kappa+theta) ≤ (NativeFiniteKakeyaCounts.multiplicity D).toReal) :
    D.thickness^(-kappa+theta+zeta) ≤ NativeIncidenceMultiplicityTower.multiplicity (retained original F) := by
  calc
    _ = D.thickness^zeta*D.thickness^(-kappa+theta) := by
      rw [←Real.rpow_add h.1.2.1]
      congr 1
      ring
    _ ≤ D.thickness^zeta*(NativeFiniteKakeyaCounts.multiplicity D).toReal :=
      mul_le_mul_of_nonneg_left hnear (Real.rpow_pos_of_pos h.1.2.1 _).le
    _ ≤ _ := original_fine_multiplicity_retention h original horiginal F hmass

end NativeCoarseFineMultiplicity
