import Theorems.Thm_StickyKakeya4_native_dense_original_parent
import Theorems.Thm_StickyKakeya4_native_original_pruned_mass
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace NativeDenseRetainedUnitParent
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeOriginalPrunedMass
open scoped BigOperators ENNReal

def parentSubset {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n)) (a : ℝ) (p : Parent) :
    Finset (Fin n) := R.filter (fun i => parentLabel D a 1 i=p)
def realShadingMass {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n)) : ℝ :=
  ∑i∈R,(volume (D.shading i)).toReal

lemma realShadingMass_eq_toReal {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) :
    realShadingMass D R=(shadingMass D R).toReal := by
  symm
  apply ENNReal.toReal_sum
  intro i _hi
  simpa only [shadingMass,Finset.sum_singleton] using shadingMass_ne_top h {i}

/-- Select within the already retained ORIGINAL labels, preserving both
actual shading mass and average original shading volume per tube. -/
theorem exists_dense_retained_parent {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (hR : R.Nonempty) (hshade : 0 < shadingMass D R) :
    ∃ p∈R.image (parentLabel D a 1), (parentSubset D R a p).Nonempty ∧
      0 < realShadingMass D (parentSubset D R a p) ∧
      realShadingMass D R ≤ 2*((R.image (parentLabel D a 1)).card:ℝ)*
        realShadingMass D (parentSubset D R a p) ∧
      realShadingMass D R*(parentSubset D R a p).card ≤ 
        2*(R.card:ℝ)*realShadingMass D (parentSubset D R a p) := by
  let P := R.image (parentLabel D a 1)
  have hm : (∑p∈P,realShadingMass D (parentSubset D R a p))=realShadingMass D R := by
    exact sum_fiberwise_of_maps_to (fun i hi=>mem_image_of_mem _ hi) _
  have hw : (∑p∈P,((parentSubset D R a p).card:ℝ))=(R.card:ℝ) := by
    exact_mod_cast (card_eq_sum_card_image (parentLabel D a 1) R).symm
  have hs : 0 < realShadingMass D R := by
    rw [realShadingMass_eq_toReal h]
    exact ENNReal.toReal_pos hshade.ne' (shadingMass_ne_top h R)
  obtain ⟨p,hp,hpos,hret,hden⟩ := NativeDenseOriginalParent.exists_mass_and_density P
    (fun p=>realShadingMass D (parentSubset D R a p))
    (fun p=>(parentSubset D R a p).card)
    (fun _ _ => sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)) (fun _ _ => Nat.cast_nonneg _)
    (by rw [hm]; exact hs) (by rw [hw]; exact_mod_cast card_pos.mpr hR)
  have hpne : (parentSubset D R a p).Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty.mp hn] at hpos
    simp only [realShadingMass,sum_empty,lt_self_iff_false] at hpos
  rw [hm] at hret hden
  rw [hw] at hden
  exact ⟨p,hp,hpne,hpos,hret,hden⟩

def realTubeMass {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n)) : ℝ :=
  ∑i∈R,(volume (markedUnitTube (D.line i) D.thickness)).toReal

lemma realTubeMass_pos {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (hR : R.Nonempty) (hsmall : D.thickness ≤ 1/8) : 0 < realTubeMass D R := by
  apply sum_pos
  · intro i _hi
    have hd := h.1.2.1
    have hl := volume_markedUnitTube_lower_bound (h.1.2.2.2.2.1 i) h.1.2.1 hsmall
    have hp : 0 < volume (markedUnitTube (D.line i) D.thickness) := lt_of_lt_of_le (by positivity) hl
    have ht : volume (markedUnitTube (D.line i) D.thickness) ≠ ⊤ :=
      ne_top_of_le_ne_top (by finiteness) (tube_volume_upper h i)
    exact ENNReal.toReal_pos hp.ne' ht
  · exact hR

/-- Choosing density with actual tube volumes removes any need to postulate
unchanged density or equal tube volumes after selecting the whole parent. -/
theorem exists_dense_retained_volume_parent {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (hR : R.Nonempty) (hshade : 0 < shadingMass D R) (hsmall : D.thickness ≤ 1/8) :
    ∃ p∈R.image (parentLabel D a 1), (parentSubset D R a p).Nonempty ∧
      0 < realShadingMass D (parentSubset D R a p) ∧
      realShadingMass D R ≤ 2*((R.image (parentLabel D a 1)).card:ℝ)*
        realShadingMass D (parentSubset D R a p) ∧
      realShadingMass D R*realTubeMass D (parentSubset D R a p) ≤ 
        2*realTubeMass D R*realShadingMass D (parentSubset D R a p) := by
  let P := R.image (parentLabel D a 1)
  have hm : (∑p∈P,realShadingMass D (parentSubset D R a p))=realShadingMass D R := by
    exact sum_fiberwise_of_maps_to (fun i hi=>mem_image_of_mem _ hi) _
  have hw : (∑p∈P,realTubeMass D (parentSubset D R a p))=realTubeMass D R := by
    exact sum_fiberwise_of_maps_to (fun i hi=>mem_image_of_mem _ hi) _
  have hs : 0 < realShadingMass D R := by
    rw [realShadingMass_eq_toReal h]
    exact ENNReal.toReal_pos hshade.ne' (shadingMass_ne_top h R)
  obtain ⟨p,hp,hpos,hret,hden⟩ := NativeDenseOriginalParent.exists_mass_and_density P
    (fun p=>realShadingMass D (parentSubset D R a p))
    (fun p=>realTubeMass D (parentSubset D R a p))
    (fun _ _ => sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))
    (fun _ _ => sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))
    (by rw [hm]; exact hs) (by rw [hw]; exact realTubeMass_pos h R hR hsmall)
  have hpne : (parentSubset D R a p).Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty.mp hn] at hpos
    simp only [realShadingMass,sum_empty,lt_self_iff_false] at hpos
  rw [hm] at hret hden
  rw [hw] at hden
  exact ⟨p,hp,hpne,hpos,hret,hden⟩

lemma retained_parent_density {n : ℕ} {D : FiniteScaleSource n} {eta lam : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (hR : R.Nonempty) (hsmall : D.thickness ≤ 1/8) (p : Parent)
    (hsource : lam*realTubeMass D R ≤ realShadingMass D R)
    (hden : realShadingMass D R*realTubeMass D (parentSubset D R a p) ≤ 
      2*realTubeMass D R*realShadingMass D (parentSubset D R a p)) :
    lam*realTubeMass D (parentSubset D R a p) ≤ 2*realShadingMass D (parentSubset D R a p) := by
  have hT := realTubeMass_pos h R hR hsmall
  have hQ : 0 ≤ realTubeMass D (parentSubset D R a p) := sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have hh := (mul_le_mul_of_nonneg_right hsource hQ).trans hden
  apply (mul_le_mul_iff_left₀ hT).mp
  nlinarith only [hh]
end NativeDenseRetainedUnitParent
