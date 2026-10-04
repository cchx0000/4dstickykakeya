import Theorems.Thm_StickyKakeya4_original_separated_packing
import Theorems.Thm_StickyKakeya4_original_tensor_frostman

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped Pointwise

namespace OriginalCoefficientRadius

/-- The radius uses only the mesh and actual pair distances, including for
an empty candidate. It is always at least the original mesh. -/
def radius (A : Finset ℝ) (delta : ℝ) : ℝ :=
  (insert delta ((A ×ˢ A).image (fun p => |p.1-p.2|))).max'
    (Finset.insert_nonempty _ _)

lemma mesh_le_radius (A : Finset ℝ) (delta : ℝ) : delta ≤ radius A delta := by
  exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)

lemma pair_le_radius (A : Finset ℝ) (delta : ℝ) {x y : ℝ}
    (hx : x∈A) (hy : y∈A) : |x-y| ≤ radius A delta := by
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,rfl⟩)

lemma radius_le (A : Finset ℝ) {delta B : ℝ} (hdelta : delta ≤ B)
    (hpair : ∀ x∈A, ∀ y∈A, |x-y| ≤ B) : radius A delta ≤ B := by
  apply Finset.max'_le
  intro r hr
  rcases Finset.mem_insert.mp hr with rfl | hr
  · exact hdelta
  · obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hr
    exact hpair x (Finset.mem_product.mp hxy).1 y (Finset.mem_product.mp hxy).2

lemma radius_mono {A D : Finset ℝ} {delta : ℝ} (hAD : A⊆D) :
    radius A delta ≤ radius D delta := by
  exact radius_le A (mesh_le_radius D delta)
    (fun _ hx _ hy => pair_le_radius D delta (hAD hx) (hAD hy))

/-- Choose a maximal-density actual subset from the original finite power
set. No Frostman estimate below an external cutoff is used. -/
theorem exists_original_maximal_density (D : Finset ℝ) {delta kappa : ℝ}
    (hD : D.Nonempty) (hdelta : 0 < delta) :
    ∃ S : Finset ℝ, S⊆D ∧ S.Nonempty ∧
      ∀ T : Finset ℝ, T⊆D →
        (T.card:ℝ)/(radius T delta)^kappa ≤ (S.card:ℝ)/(radius S delta)^kappa := by
  obtain ⟨S,hS,hmax⟩ := Finset.exists_max_image D.powerset
    (fun T => (T.card:ℝ)/(radius T delta)^kappa)
    ⟨D,Finset.mem_powerset.mpr Finset.Subset.rfl⟩
  have hpositive : 0 < (D.card:ℝ)/(radius D delta)^kappa :=
    div_pos (Nat.cast_pos.mpr hD.card_pos)
      (Real.rpow_pos_of_pos (hdelta.trans_le (mesh_le_radius D delta)) _)
  have hSpos : 0 < (S.card:ℝ)/(radius S delta)^kappa :=
    hpositive.trans_le (hmax D (Finset.mem_powerset.mpr Finset.Subset.rfl))
  have hSne : S.Nonempty := by
    by_contra h
    have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he,Finset.card_empty,Nat.cast_zero,zero_div,lt_self_iff_false] at hSpos
  exact ⟨S,Finset.mem_powerset.mp hS,hSne,
    fun T hT => hmax T (Finset.mem_powerset.mpr hT)⟩

/-- Separation of the original carrier supplies packing for the selected
actual subset at its own radius. -/
theorem original_radius_packing (S : Finset ℝ) {delta : ℝ} (hdelta : 0 < delta)
    (hS : S.Nonempty)
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → delta ≤ |x-y|) :
    (S.card:ℝ) ≤ 4*radius S delta/delta := by
  obtain ⟨c,hc⟩ := hS
  have hr := hdelta.trans_le (mesh_le_radius S delta)
  have he : S.filter (fun x => |x-c| ≤ radius S delta)=S := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    exact pair_le_radius S delta hx hc
  have hp := OriginalSeparatedPacking.scalar_ball_card S hdelta hr.le hsep c
  rw [he] at hp
  have hratio : 1 ≤ radius S delta/delta := (le_div_iff₀ hdelta).mpr (by
    simpa only [one_mul] using mesh_le_radius S delta)
  rw [mul_div_assoc]
  linarith only [hp,hratio]

end OriginalCoefficientRadius
