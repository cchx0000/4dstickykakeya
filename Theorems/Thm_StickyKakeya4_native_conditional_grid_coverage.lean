import Theorems.Thm_StickyKakeya4_native_angular_dyadic_interpolation
import Theorems.Thm_StickyKakeya4_native_fixed_size_scale_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeConditionalGridCoverage
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeConditionalReferenceMenu NativeMiddleGrainParentBudget

lemma gridDepth_schedule (m K : ℕ) (j : Fin (K+1)) :
    gridDepth m K j=6+(NativeFixedSizeScaleMenu.schedule K (m-6) j).val := by
  simp only [gridDepth,NativeFixedSizeScaleMenu.schedule,Nat.mul_comm]

lemma exists_grid_predecessor (m K d : ℕ) (hK : 0< K) (hd : 6≤ d) (hdm : d≤ m) :
    ∃j : Fin (K+1),gridDepth m K j≤ d ∧
      ((d-gridDepth m K j:ℕ):ℝ)≤ ((m-6:ℕ):ℝ)/K+1 := by
  by_cases hm : m=6
  · have hd6 : d=6 := by omega
    refine ⟨0,?_,?_⟩ <;> simp [gridDepth,hm,hd6]
  · have hlevel : 0< m-6 := by omega
    obtain ⟨j,hj,_hgap,hgapR⟩ := NativeFixedSizeScaleMenu.exists_predecessor K (m-6) (d-6)
      hK hlevel (by omega)
    refine ⟨j,?_,?_⟩
    · rw [gridDepth_schedule]
      omega
    · have hid : d-gridDepth m K j=d-6-(NativeFixedSizeScaleMenu.schedule K (m-6) j).val := by
        rw [gridDepth_schedule]
        omega
      rwa [hid]

def queryIndex {g K : ℕ} (i : Fin (g+1)) (j k : Fin (K+1)) : Fin (queryCount g K) :=
  finProdFinEquiv (i,finProdFinEquiv (j,k))

lemma queryIndex_candidate {g K : ℕ} (i : Fin (g+1)) (j k : Fin (K+1)) :
    candidate (queryIndex i j k)=i := by simp only [candidate,queryIndex,Equiv.symm_apply_apply]

lemma queryIndex_pair {g K : ℕ} (i : Fin (g+1)) (j k : Fin (K+1)) :
    pair (queryIndex i j k)=(j,k) := by simp only [pair,queryIndex,Equiv.symm_apply_apply]

/-- Every dyadic rho/sigma pair has a preceding pair in the fixed source
menu. Both explicit depth gaps are at most (m-6)/K+1; no extra relation is
installed after the first core has been chosen. -/
theorem exists_query_predecessors {g K level : ℕ}
    (schedule : Fin (g+1) → Fin (level+1)) (i : Fin (g+1)) (hK : 0< K)
    (s t : ℕ) (ht : 6≤ t) (hts : t≤ s) (hsm : s≤ middleDepth (schedule i).val) :
    ∃q : Fin (queryCount g K),candidate q=i ∧
      rhoDepth schedule q≤ s ∧ sigmaDepth schedule q≤ t ∧
      ((s-rhoDepth schedule q:ℕ):ℝ)≤ ((middleDepth (schedule i).val-6:ℕ):ℝ)/K+1 ∧
      ((t-sigmaDepth schedule q:ℕ):ℝ)≤ ((middleDepth (schedule i).val-6:ℕ):ℝ)/K+1 := by
  let m := middleDepth (schedule i).val
  obtain ⟨j,hjs,hjg⟩ := exists_grid_predecessor m K s hK (by omega) hsm
  obtain ⟨k,hkt,hkg⟩ := exists_grid_predecessor m K t hK ht (hts.trans hsm)
  let q := queryIndex i j k
  have hqi : candidate q=i := queryIndex_candidate i j k
  have hqp : pair q=(j,k) := queryIndex_pair i j k
  have hqm : outerDepth schedule q=m := by simp only [outerDepth,hqi,m]
  have hqs : rhoDepth schedule q=max (gridDepth m K j) (gridDepth m K k) := by
    simp only [rhoDepth,hqm,hqp]
  have hqt : sigmaDepth schedule q=min (gridDepth m K j) (gridDepth m K k) := by
    simp only [sigmaDepth,hqm,hqp]
  refine ⟨q,hqi,?_,?_,?_,?_⟩
  · rw [hqs]
    omega
  · rw [hqt]
    omega
  · have hh : s-rhoDepth schedule q≤ s-gridDepth m K j := by rw [hqs]; omega
    exact (Nat.cast_le.mpr hh).trans hjg
  · have hh : t-sigmaDepth schedule q≤ max (s-gridDepth m K j) (t-gridDepth m K k) := by
      rw [hqt]
      omega
    have hhR : ((t-sigmaDepth schedule q:ℕ):ℝ)≤
        max ((s-gridDepth m K j:ℕ):ℝ) ((t-gridDepth m K k:ℕ):ℝ) := by exact_mod_cast hh
    exact hhR.trans (max_le hjg hkg)

end NativeConditionalGridCoverage
