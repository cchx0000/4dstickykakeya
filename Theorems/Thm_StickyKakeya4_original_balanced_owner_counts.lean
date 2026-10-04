import Theorems.Thm_StickyKakeya4_original_finite_cell_weights
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000
noncomputable section
open scoped BigOperators
namespace OriginalBalancedOwnerCounts
open Classical OriginalFiniteCellWeights
variable {α β : Type*} [DecidableEq β]

lemma original_owner_mass_bounds (U : Finset α) (C : Finset β) (owner : α → β)
    (M A : ℝ) (hmap : ∀ x∈U,owner x∈C)
    (hmin : ∀ c∈C,M ≤ pointWeight U owner c)
    (hmax : ∀ c∈C,pointWeight U owner c ≤ A*M) :
    M*C.card ≤ (U.card : ℝ) ∧ (U.card : ℝ) ≤ A*M*C.card := by
  have hfilter : U.filter (fun x => owner x∈C)=U := Finset.filter_eq_self.mpr hmap
  have hs := point_subset_mass_readback U owner C
  rw [hfilter] at hs
  constructor
  · have hh := Finset.sum_le_sum hmin
    rw [hs] at hh
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using hh
  · have hh := Finset.sum_le_sum hmax
    rw [hs] at hh
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using hh

/-- Dense original edges force the actual full-owner carrier to retain
ambient mass. No source normalization is changed. -/
theorem original_dense_carrier_mass (Q U : Finset α) (G : Finset (α × α))
    (lam : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hG : G⊆U.product U) (hdense : lam*(Q.card : ℝ)^2 ≤ G.card) :
    lam*Q.card ≤ (U.card : ℝ) := by
  have hcard : (G.card : ℝ) ≤ (U.card : ℝ)^2 := by
    have hh := (Finset.card_le_card hG).trans_eq (Finset.card_product _ _)
    simpa only [pow_two,Nat.cast_mul] using (Nat.cast_le.mpr hh : (G.card : ℝ) ≤ (U.card*U.card : ℕ))
  have hll : lam^2 ≤ lam := by nlinarith only [hlam,hlam1]
  have hs := mul_le_mul_of_nonneg_right hll (sq_nonneg (Q.card : ℝ))
  have hnon : 0 ≤ lam*Q.card := mul_nonneg hlam (Nat.cast_nonneg _)
  have hu : 0 ≤ (U.card : ℝ) := Nat.cast_nonneg _
  nlinarith only [hs,hdense,hcard,hnon,hu]

/-- Exact full-fiber balance converts the ORIGINAL graph into a genuinely
unweighted owner-pair image with the stated density loss. -/
theorem original_unweighted_owner_graph (Q U : Finset α) (C : Finset β)
    (G : Finset (α × α)) (owner : α → β) (M A lam : ℝ)
    (hM : 0 < M) (hA : 0 ≤ A) (hlam : 0 ≤ lam)
    (hUQ : U⊆Q) (hG : G⊆U.product U) (hmap : ∀ x∈U,owner x∈C)
    (hmin : ∀ c∈C,M ≤ pointWeight U owner c)
    (hmax : ∀ c∈C,pointWeight U owner c ≤ A*M)
    (hdense : lam*(Q.card : ℝ)^2 ≤ G.card) :
    lam*(C.card : ℝ)^2 ≤ A^2*(occupied G (pairCode owner)).card := by
  have hmass := original_owner_mass_bounds U C owner M A hmap hmin hmax
  have hQ : M*C.card ≤ (Q.card : ℝ) :=
    hmass.1.trans (Nat.cast_le.mpr (Finset.card_le_card hUQ))
  have hsq := pow_le_pow_left₀ (mul_nonneg hM.le (Nat.cast_nonneg C.card)) hQ 2
  have hlo := (mul_le_mul_of_nonneg_left hsq hlam).trans hdense
  have hp (z : β × β) (hz : z∈occupied G (pairCode owner)) : pairWeight G owner z ≤ (A*M)^2 := by
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨he1,he2⟩ := Finset.mem_product.mp (hG he)
    have hpair := pairWeight_le_pointWeight_product U G owner hG (pairCode owner e)
    have hh := mul_le_mul (hmax (owner e.1) (hmap e.1 he1))
      (hmax (owner e.2) (hmap e.2 he2)) (pointWeight_nonneg U owner (owner e.2))
      (mul_nonneg hA hM.le)
    exact hpair.trans (by simpa only [pairCode,pow_two] using hh)
  have hhi : (G.card : ℝ) ≤ (A*M)^2*(occupied G (pairCode owner)).card := by
    rw [← pair_mass_readback G owner]
    have hh := Finset.sum_le_sum hp
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using hh
  apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hM)).mp
  nlinarith only [hlo,hhi]

/-- Rich original points remain rich after the owner map. The lower mass
normalization is ambient Q, so no additional Q/core tax is introduced. -/
theorem original_owner_rich_image (Q U X : Finset α) (C : Finset β)
    (owner : α → β) (M A k : ℝ) (hM : 0 < M) (hk : 0 ≤ k)
    (hUQ : U⊆Q) (hXU : X⊆U) (hmap : ∀ x∈U,owner x∈C)
    (hmin : ∀ c∈C,M ≤ pointWeight U owner c)
    (hmax : ∀ c∈C,pointWeight U owner c ≤ A*M)
    (hrich : k*Q.card ≤ (X.card : ℝ)) :
    k*C.card ≤ A*(occupied X owner).card := by
  have hmass := original_owner_mass_bounds U C owner M A hmap hmin hmax
  have hQ : M*C.card ≤ (Q.card : ℝ) :=
    hmass.1.trans (Nat.cast_le.mpr (Finset.card_le_card hUQ))
  have hlo := (mul_le_mul_of_nonneg_left hQ hk).trans hrich
  have hpoint (c : β) (hc : c∈occupied X owner) : pointWeight X owner c ≤ A*M := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hc
    have hsub : pointFiber X owner (owner x)⊆pointFiber U owner (owner x) := by
      intro y hy
      obtain ⟨hyX,hyc⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨hXU hyX,hyc⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hmax (owner x) (hmap x (hXU hx)))
  have hhi : (X.card : ℝ) ≤ A*M*(occupied X owner).card := by
    rw [← point_mass_readback X owner]
    have hh := Finset.sum_le_sum hpoint
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using hh
  apply (mul_le_mul_iff_of_pos_left hM).mp
  nlinarith only [hlo,hhi]

/-- Original mass control transfers any actual owner-region count. The
region's full preimage must be charged in Q; no arbitrary fiber cap is assumed. -/
theorem original_owner_region_count (Q U : Finset α) (C D : Finset β)
    (owner : α → β) (M A lam B : ℝ) (hM : 0 < M) (hB : 0 ≤ B) (hlam : 0 ≤ lam)
    (hDC : D⊆C) (hmap : ∀ x∈U,owner x∈C)
    (hmin : ∀ c∈C,M ≤ pointWeight U owner c)
    (hmax : ∀ c∈C,pointWeight U owner c ≤ A*M)
    (hambient : lam*Q.card ≤ (U.card : ℝ))
    (hcap : ((U.filter (fun x => owner x∈D)).card : ℝ) ≤ B*Q.card) :
    lam*D.card ≤ A*B*C.card := by
  have hlo : M*D.card ≤ ((U.filter (fun x => owner x∈D)).card : ℝ) := by
    rw [← point_subset_mass_readback U owner D]
    have hh := Finset.sum_le_sum (fun c hc => hmin c (hDC hc))
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using hh
  have hmass := (original_owner_mass_bounds U C owner M A hmap hmin hmax).2
  have h1 := mul_le_mul_of_nonneg_left (hlo.trans hcap) hlam
  have h2 := mul_le_mul_of_nonneg_left hambient hB
  have h3 := mul_le_mul_of_nonneg_left hmass hB
  apply (mul_le_mul_iff_of_pos_left hM).mp
  nlinarith only [h1,h2,h3]

end OriginalBalancedOwnerCounts
