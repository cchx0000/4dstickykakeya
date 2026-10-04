import Theorems.Thm_StickyKakeya4_original_three_dimensional_shade_local_count
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4200000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalFiniteShadeUnion
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeParameters
open OriginalThreeDimensionalTubeCells OriginalThreeDimensionalShadeLocalCount
open OriginalThreeDimensionalTubePairCount

/-- A universal finite union estimate for ACTUAL original, cube-injective
shadings. It is derived from short-pair deletion and the proved original
pair/tube multiplicity, without a planar or Katz--Tao premise. -/
theorem original_finite_shade_union (R : Finset Pair3) (Y : Pair3→Finset Point3)
    (rho b : ℝ) (i : Fin 3) (hrho : 0<rho) (hrho1 : rho≤1)
    (hb : 0<b) (hsmall : rho≤b/4800)
    (hne : ∀ z∈R, z.2 i-z.1 i≠0)
    (hmax : ∀ z∈R, ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|)
    (hcell : Set.InjOn (parameterCell rho i) R)
    (hshade : ∀ z∈R, ∀ x∈Y z, x∈physicalTube3 z.1 z.2 (4*rho))
    (hbox : ∀ z∈R, ∀ x∈Y z, ∀ j, |x j|≤1)
    (hinj : ∀ z∈R, Set.InjOn (cell rho) (Y z))
    (hmass : ∀ z∈R, b≤rho*(Y z).card) :
    (R.card : ℝ)*b^4≤100000000000000000*rho^2*((R.biUnion Y).card : ℝ)^2 := by
  let a := b/4800
  let U := R.biUnion Y
  let F := farPairs U a
  let I : Finset (Σ _z : Pair3, Pair3) := R.sigma (fun z => farPairs (Y z) a)
  have ha : 0<a := by dsimp [a]; positivity
  have hUbox (x : Point3) (hx : x∈U) : ∀ j, |x j|≤1 := by
    obtain ⟨z,hz,hxY⟩ := Finset.mem_biUnion.mp hx
    exact hbox z hz x hxY
  have hIcard : (I.card : ℝ)=∑ z∈R,((farPairs (Y z) a).card : ℝ) := by
    simp only [I,Finset.card_sigma,Nat.cast_sum]
  have hlower : (R.card : ℝ)*b^2≤2*rho^2*I.card := by
    rw [hIcard,Finset.mul_sum]
    calc
      _ = ∑ _z∈R, b^2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun z hz =>
        original_shade_far_pairs (Y z) z i rho b hrho hb hsmall
          (hne z hz) (hmax z hz) (hinj z hz) (hshade z hz) (hmass z hz))
  have hIupper : (I.card : ℝ)≤(F.card : ℝ)*(1000000000/a^2) := by
    apply FiniteTransverseMenuGrowth.card_le_real_mul_of_fibers I F (fun w => w.2) _
    · intro w hw
      obtain ⟨hz,hwfar⟩ := Finset.mem_sigma.mp hw
      obtain ⟨hxy,hfar⟩ := Finset.mem_filter.mp hwfar
      obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_biUnion.mpr ⟨w.1,hz,hx⟩,Finset.mem_biUnion.mpr ⟨w.1,hz,hy⟩⟩,hfar⟩
    · intro xy hxy
      let B := I.filter (fun w => w.2=xy)
      have hBinj : Set.InjOn (fun w : Σ _z : Pair3, Pair3 => w.1) B := by
        intro u hu v hv huv
        have hu2 := (Finset.mem_filter.mp hu).2
        have hv2 := (Finset.mem_filter.mp hv).2
        exact Sigma.ext huv (heq_of_eq (hu2.trans hv2.symm))
      have hsub : B.image (fun w => w.1)⊆tubesThroughPair R rho xy.1 xy.2 := by
        intro z hz
        obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨hwI,hwxy⟩ := Finset.mem_filter.mp hw
        obtain ⟨hwR,hwfar⟩ := Finset.mem_sigma.mp hwI
        rw [hwxy] at hwfar
        obtain ⟨hpoints,_hfar⟩ := Finset.mem_filter.mp hwfar
        obtain ⟨hx,hy⟩ := Finset.mem_product.mp hpoints
        have grow (p : Point3) (hp : p∈Y w.1) : p∈physicalTube3 w.1.1 w.1.2 (8*rho) := by
          obtain ⟨l,hl⟩ := hshade w.1 hwR p hp
          exact ⟨l,hl.trans (by linarith only [hrho])⟩
        exact Finset.mem_filter.mpr ⟨hwR,grow xy.1 hx,grow xy.2 hy⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_image_of_injOn hBinj] at hc
      obtain ⟨hxyU,hfar⟩ := Finset.mem_filter.mp hxy
      obtain ⟨hxU,hyU⟩ := Finset.mem_product.mp hxyU
      have ht := original_tubes_through_pair_card R rho i xy.1 xy.2 hrho hrho1
        (hUbox xy.1 hxU) (hUbox xy.2 hyU) hne hmax hcell
      have hbnd : 1000000000/(max (distance3 xy.1 xy.2) rho)^2≤1000000000/a^2 := by
        apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos ha)
        exact pow_le_pow_left₀ ha.le (hfar.trans (le_max_left _ _)) 2
      exact (Nat.cast_le.mpr hc).trans (ht.trans hbnd)
  have hFcard : (F.card : ℝ)≤(U.card : ℝ)^2 := by
    have hh := Finset.card_le_card (Finset.filter_subset (fun z => a≤distance3 z.1 z.2) (U.product U))
    simpa only [Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul,pow_two] using (Nat.cast_le.mpr hh :
      ((farPairs U a).card : ℝ)≤((U.product U).card : ℝ))
  have hupper := hIupper.trans (mul_le_mul_of_nonneg_right hFcard (by positivity : 0≤1000000000/a^2))
  have hupper' : (I.card : ℝ)*a^2≤1000000000*(U.card : ℝ)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos ha)).mp
    convert hupper using 1; ring
  have h1 := mul_le_mul_of_nonneg_right hlower (sq_nonneg a)
  have h2 := mul_le_mul_of_nonneg_left hupper' (show 0≤2*rho^2 by positivity)
  dsimp [a] at h1 h2
  have hnon : 0≤rho^2*(U.card : ℝ)^2 := by positivity
  change (R.card : ℝ)*b^4≤100000000000000000*rho^2*(U.card : ℝ)^2
  nlinarith only [h1,h2,hnon]

end OriginalThreeDimensionalFiniteShadeUnion
