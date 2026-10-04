import Theorems.Thm_StickyKakeya4_original_high_dimensional_projection_energy
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
open Classical
open scoped BigOperators

namespace OriginalTensorProjectionSelection
open ActualRoundedAdditiveEnergy GKZOriginalGapEnergy OriginalTensorFrostman
open OriginalPolynomialCoefficientGrid OriginalTensorProjectionPairs OriginalTensorQuadraticCaps
open OriginalHighDimensionalProjectionEnergy

/-- Actual original weak scalar caps, multiplied in the original tensor,
yield the full parameter collision energy. No energy certificate is assumed. -/
theorem original_tensor_collision_energy (A : Finset ℝ) (n M k : ℕ)
    {K u : ℝ} (hK : 1 ≤ K) (hmu : 2 ≤ u*((n+1:ℕ):ℝ))
    (hmesh : FinitePlaneProjectionGrid.mesh M ≤ ProjectionAnnulusEnergy.mesh k)
    (hbox : ∀ a∈A, |a| ≤ 1)
    (hprofile : ScalarFrostman A (ProjectionAnnulusEnergy.mesh k) K u) :
    (∑ v∈parameters n M,
      ((labelCollisions (tensor A (n+1)) v (ProjectionAnnulusEnergy.mesh k)).card:ℝ)) ≤
      128*K^(n+1)*ProjectionAnnulusEnergy.mesh k*((tensor A (n+1)).card:ℝ)^2*
        (parameters n M).card := by
  apply original_quadratic_projection_energy (tensor A (n+1)) M k
    (pow_nonneg (le_trans (by norm_num) hK) _) hmesh
  · intro x hx y hy i
    have hxB := hbox (x i) (Fintype.mem_piFinset.mp hx i)
    have hyB := hbox (y i) (Fintype.mem_piFinset.mp hy i)
    have ht := abs_sub_le (y i) 0 (x i)
    simp only [sub_zero,zero_sub,abs_neg] at ht
    linarith only [hxB,hyB,ht]
  · intro x _hx r hr
    have he : (tensor A (n+1)).filter (OriginalTensorProjectionPairs.close r x) =
        (tensor A (n+1)).filter (fun a => ∀ i, |a i-x i| ≤ r) := by
      ext a
      simp only [Finset.mem_filter,OriginalTensorProjectionPairs.close]
    rw [he]
    exact original_tensor_allscale_quadratic A (n+1)
      (ProjectionAnnulusEnergy.mesh_pos k) hK hmu hprofile x r hr

/-- A genuine finite initial projection for the polynomial engine. The
coefficient grid and its member are constructed from the original scalar
carrier; its weak exponent need not match its cardinality exponent. -/
theorem exists_original_tensor_projection (A : Finset ℝ) (n k : ℕ)
    {K u : ℝ} (hA : A.Nonempty) (hK : 1 ≤ K) (hmu : 2 ≤ u*((n+1:ℕ):ℝ))
    (hbox : ∀ a∈A, |a| ≤ 1)
    (hprofile : ScalarFrostman A (ProjectionAnnulusEnergy.mesh k) K u) :
    ∃ v∈parameters n ⌈1/ProjectionAnnulusEnergy.mesh k⌉₊,
      (∀ i, (1/2:ℝ) ≤ v i ∧ v i ≤ 1) ∧
      1/(128*K^(n+1)) ≤ ProjectionAnnulusEnergy.mesh k*
        ((tensor A (n+1)).image (fun a => rounded (ProjectionAnnulusEnergy.mesh k)
          (projection v a))).card := by
  let delta := ProjectionAnnulusEnergy.mesh k
  let M := ⌈1/delta⌉₊
  let P := tensor A (n+1)
  let G := parameters n M
  let C : ℝ := 128*K^(n+1)*delta*(P.card:ℝ)^2
  have hd : 0 < delta := ProjectionAnnulusEnergy.mesh_pos k
  have hmesh : FinitePlaneProjectionGrid.mesh M ≤ delta := coefficient_mesh_choice hd
  have hbudget := original_tensor_collision_energy A n M k hK hmu hmesh hbox hprofile
  change (∑ v∈G, ((labelCollisions P v delta).card:ℝ)) ≤ C*G.card at hbudget
  have hP : P.Nonempty := Fintype.piFinset_nonempty.mpr (fun _ => hA)
  have hgrid : (grid M).Nonempty := Finset.card_pos.mp (by rw [grid_card]; omega)
  have hG : G.Nonempty := Fintype.piFinset_nonempty.mpr (fun _ => hgrid)
  obtain ⟨v,hv,henergy⟩ := FinitePlaneProjectionGrid.exists_le_average G
    (fun v => ((labelCollisions P v delta).card:ℝ)) C hG hbudget
  have hCS := original_projected_cell_energy P v hd
  have hprod := mul_le_mul_of_nonneg_left henergy
    (show 0 ≤ ((P.image (fun a => rounded delta (projection v a))).card:ℝ) from Nat.cast_nonneg _)
  dsimp [C] at hprod
  have hN : (0:ℝ) < P.card := Nat.cast_pos.mpr hP.card_pos
  have hone : 1 ≤ (128*K^(n+1))*delta*
      ((P.image (fun a => rounded delta (projection v a))).card:ℝ) := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hN)).mp
    nlinarith only [hCS,hprod]
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hden : 0 < 128*K^(n+1) := by positivity
  have hgain : 1/(128*K^(n+1)) ≤ delta*
      ((P.image (fun a => rounded delta (projection v a))).card:ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hone]
  refine ⟨v,hv,?_,hgain⟩
  intro i
  exact grid_bounds (Fintype.mem_piFinset.mp hv i)

end OriginalTensorProjectionSelection
