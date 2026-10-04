import Theorems.Thm_StickyKakeya4_native_original_slope_cube_packing
import Theorems.Thm_StickyKakeya4_native_dense_retained_unit_parent
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000
noncomputable section
namespace NativePaddedSourceCountBudget
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeOriginalCellChartGeometry
open NativeOriginalSlopeCubePacking NativeDenseRetainedUnitParent
open scoped BigOperators

/-- Actual original direction packing gives a global cubic source count,
independently of affine marks, offsets, or a containing compact set. -/
theorem original_card_upper {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) :
    (n:ℝ) ≤ 373248*(1/D.thickness)^3 := by
  have hb := native_cube_card_le_ratio h (univ : Finset (Fin n))
    (rho:=4) (by linarith [h.1.2.2.1]) (fun _ => -2) (by
      intro i _hi j
      have hh := abs_le.mp (slope_bound (D.line i) (h.1.2.2.2.2.1 i) (h.2.1.1 i) j)
      exact ⟨hh.1,by linarith [hh.2]⟩)
  simp only [card_univ,Fintype.card_fin] at hb
  exact hb.trans_eq (by ring)

/-- Consume the already derived original ancestor lower estimates at the
literal unit-parent level. This is not a new output regularity hypothesis. -/
lemma unit_lower_of_ancestors {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (a zeta : ℝ) (level : ℕ)
    (H : ∀ell : Fin (level+1),∀q : Parent,
      (R.filter (fun j => parentLabel D a (2^ell.val) j=q)).Nonempty →
        D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun j => parentLabel D a (2^ell.val) j=q)).card:ℝ)) :
    ∀p : Parent,(parentSubset D R a p).Nonempty →
      D.thickness^zeta*(1/D.thickness)^3 ≤ ((parentSubset D R a p).card:ℝ) := by
  intro p hp
  have hh := H ⟨0,Nat.succ_pos level⟩ p (by simpa only [parentSubset,pow_zero] using hp)
  simpa only [parentSubset,pow_zero,Nat.cast_one,one_div_one] using hh

/-- The number of occupied whole original unit parents is genuinely bounded
by the original tube count divided by their proved lower occupancy. -/
theorem unit_parent_count_bound {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (H : ∀p : Parent,(parentSubset D R a p).Nonempty →
      D.thickness^zeta*(1/D.thickness)^3 ≤ ((parentSubset D R a p).card:ℝ)) :
    ((R.image (parentLabel D a 1)).card:ℝ) ≤ 373248*D.thickness^(-zeta) := by
  let P := R.image (parentLabel D a 1)
  have hd:=h.1.2.1
  have hp : 0 < D.thickness^zeta := Real.rpow_pos_of_pos hd _
  have hsum : (∑p∈P,((parentSubset D R a p).card:ℝ))=(R.card:ℝ) := by
    exact_mod_cast (card_eq_sum_card_image (parentLabel D a 1) R).symm
  have hl : (P.card:ℝ)*(D.thickness^zeta*(1/D.thickness)^3) ≤
      373248*(1/D.thickness)^3 := by
    calc
      _ = ∑_p∈P,D.thickness^zeta*(1/D.thickness)^3 := by simp
      _ ≤ ∑p∈P,((parentSubset D R a p).card:ℝ) := by
        apply sum_le_sum
        intro p hpP
        obtain ⟨i,hi,hpi⟩ := mem_image.mp hpP
        exact H p ⟨i,mem_filter.mpr ⟨hi,hpi⟩⟩
      _ = (R.card:ℝ) := hsum
      _ ≤ n := by
        have hh : R.card ≤ n := by simpa only [card_univ,Fintype.card_fin] using card_le_card (subset_univ R)
        exact_mod_cast hh
      _ ≤ _ := original_card_upper h
  have hc : (P.card:ℝ)*D.thickness^zeta ≤ 373248 := by
    apply (mul_le_mul_iff_left₀ (show 0 < (1/D.thickness)^3 by positivity)).mp
    simpa only [mul_assoc] using hl
  change (P.card:ℝ) ≤ _
  rw [Real.rpow_neg hd.le,←div_eq_mul_inv]
  exact (le_div_iff₀ hp).mpr hc

/-- Every occupied selected original unit parent retains a proved subpower
fraction of the ORIGINAL tube labels. The actual count, not a requested
retention coefficient, supplies the CW denominator conversion. -/
theorem selected_parent_card_retention {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (H : ∀p : Parent,(parentSubset D R a p).Nonempty →
      D.thickness^zeta*(1/D.thickness)^3 ≤ ((parentSubset D R a p).card:ℝ))
    (p : Parent) (hp : (parentSubset D R a p).Nonempty) :
    (n:ℝ) ≤ 373248*D.thickness^(-zeta)*(parentSubset D R a p).card := by
  have hd:=h.1.2.1
  have hz := Real.rpow_pos_of_pos hd zeta
  calc
    _ ≤ 373248*(1/D.thickness)^3 := original_card_upper h
    _ = (373248*D.thickness^(-zeta))*(D.thickness^zeta*(1/D.thickness)^3) := by
      rw [Real.rpow_neg hd.le]
      field_simp [hz.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left (H p hp) (by positivity)
end NativePaddedSourceCountBudget
