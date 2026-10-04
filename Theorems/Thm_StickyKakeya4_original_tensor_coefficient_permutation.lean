import Theorems.Thm_StickyKakeya4_original_tensor_coefficient_collision
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped BigOperators

namespace OriginalTensorCoefficientPermutation
open OriginalTensorFrostman OriginalPolynomialCoefficientGrid OriginalTensorCoefficientCollision

/-- Permuting the actual coefficient coordinates preserves the complete
original tensor count, including all projection collisions. -/
lemma original_coefficient_permutation_card (n M : ℕ) (d : Fin (n+1) → ℝ)
    (e : Fin (n+1) ≃ Fin (n+1)) (r : ℝ) :
    ((tensor (grid M) (n+1)).filter (fun v => |∑ i, v i*d i| ≤ r)).card=
      ((tensor (grid M) (n+1)).filter (fun v => |∑ i, v i*d (e i)| ≤ r)).card := by
  let perm := fun v : Fin (n+1) → ℝ => fun i => v (e i)
  have hdot (v : Fin (n+1) → ℝ) :
      (∑ i, perm v i*d (e i))=∑ i, v i*d i :=
    e.sum_comp (fun i => v i*d i)
  apply Finset.card_bij (fun v _hv => perm v)
  · intro v hv
    obtain ⟨hvT,hnear⟩ := Finset.mem_filter.mp hv
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun i => Fintype.mem_piFinset.mp hvT (e i)),?_⟩
    rw [hdot]
    exact hnear
  · intro v _hv w _hw he
    funext i
    have hh := congrFun he (e.symm i)
    simpa only [perm,e.apply_symm_apply] using hh
  · intro w hw
    obtain ⟨hwT,hnear⟩ := Finset.mem_filter.mp hw
    let v : Fin (n+1) → ℝ := fun i => w (e.symm i)
    have he : perm v=w := by funext i; simp only [perm,v,e.symm_apply_apply]
    refine ⟨v,Finset.mem_filter.mpr ⟨?_,?_⟩,he⟩
    · exact Fintype.mem_piFinset.mpr (fun i => Fintype.mem_piFinset.mp hwT (e.symm i))
    · have hh := hdot v
      rw [he] at hh
      rw [hh] at hnear
      exact hnear

/-- Every nonzero original coordinate gives the same literal tensor
collision bound; an actual coordinate swap reduces to the proved row count. -/
theorem original_tensor_coordinate_collision (n M : ℕ) (d : Fin (n+1) → ℝ)
    (j : Fin (n+1)) {r : ℝ} (hr : 0 ≤ r) (hd : d j≠0) :
    (((tensor (grid M) (n+1)).filter (fun v => |∑ i, v i*d i| ≤ r)).card:ℝ) ≤
      (4*r/|d j|+2*FinitePlaneProjectionGrid.mesh M)*(tensor (grid M) (n+1)).card := by
  let e := Equiv.swap (0 : Fin (n+1)) j
  rw [original_coefficient_permutation_card n M d e r]
  have he : e 0=j := Equiv.swap_apply_left _ _
  have hnon : (fun i => d (e i)) 0≠0 := by simpa only [he] using hd
  have hh := original_tensor_first_collision n M (fun i => d (e i)) hr hnon
  simpa only [he] using hh

/-- With the explicitly chosen coefficient mesh, a single original secant
has collision fraction at most 6delta/its coordinate length. -/
theorem original_tensor_small_mesh_collision (n M : ℕ) (d : Fin (n+1) → ℝ)
    (j : Fin (n+1)) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hd : d j≠0) (hd1 : |d j| ≤ 1)
    (hmesh : FinitePlaneProjectionGrid.mesh M ≤ delta) :
    (((tensor (grid M) (n+1)).filter (fun v => |∑ i, v i*d i| ≤ delta)).card:ℝ) ≤
      (6*delta/|d j|)*(tensor (grid M) (n+1)).card := by
  have hh := original_tensor_coordinate_collision n M d j hdelta hd
  have hscale : delta ≤ delta/|d j| := by
    apply (le_div_iff₀ (abs_pos.mpr hd)).mpr
    exact mul_le_of_le_one_right hdelta hd1
  have hfactor : 4*delta/|d j|+2*FinitePlaneProjectionGrid.mesh M ≤ 6*delta/|d j| := by
    simp only [mul_div_assoc]
    linarith only [hmesh,hscale]
  exact hh.trans (mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg _))


/-- The symmetric unit box has coordinate differences at most two; the same
actual grid calculation then gives the explicit factor eight. -/
theorem original_tensor_two_box_collision (n M : ℕ) (d : Fin (n+1) → ℝ)
    (j : Fin (n+1)) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hd : d j≠0) (hd2 : |d j| ≤ 2)
    (hmesh : FinitePlaneProjectionGrid.mesh M ≤ delta) :
    (((tensor (grid M) (n+1)).filter (fun v => |∑ i, v i*d i| ≤ delta)).card:ℝ) ≤
      (8*delta/|d j|)*(tensor (grid M) (n+1)).card := by
  have hh := original_tensor_coordinate_collision n M d j hdelta hd
  have hscale : delta ≤ 2*delta/|d j| := by
    apply (le_div_iff₀ (abs_pos.mpr hd)).mpr
    have ht := mul_le_mul_of_nonneg_left hd2 hdelta
    nlinarith only [ht]
  have hfactor : 4*delta/|d j|+2*FinitePlaneProjectionGrid.mesh M ≤ 8*delta/|d j| := by
    simp only [mul_div_assoc] at hscale ⊢
    linarith only [hmesh,hscale]
  exact hh.trans (mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg _))

end OriginalTensorCoefficientPermutation
