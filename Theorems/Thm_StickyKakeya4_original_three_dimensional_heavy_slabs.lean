import Theorems.Thm_StickyKakeya4_original_three_dimensional_direction_grid
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalHeavySlabs
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid

abbrev Pair3 := Point3 × Point3
def slabCode (rho : ℝ) (d : DirectionLabel) (p : Point3) : ℤ := ⌊value rho d p/rho⌋
def slabPoints (P : Finset Point3) (rho : ℝ) (d : DirectionLabel) (k : ℤ) : Finset Point3 :=
  P.filter (fun p => |value rho d p-rho*k|≤3*rho)
def heavyWitness (P : Finset Point3) (rho H : ℝ) (d : DirectionLabel) (z : Pair3) : Prop :=
  ∃ k∈P.image (slabCode rho d), H≤((slabPoints P rho d k).card : ℝ) ∧
    z.1∈slabPoints P rho d k ∧ z.2∈slabPoints P rho d k
def nonheavyPartners (P : Finset Point3) (rho H : ℝ) (d : DirectionLabel) (p : Point3) : Finset Point3 :=
  P.filter (fun q => d∈pairBand rho p q ∧ ¬heavyWitness P rho H d (p,q))

theorem own_slab_contains_band (P : Finset Point3) (rho : ℝ) (d : DirectionLabel)
    (p q : Point3) (hrho : 0<rho) (hp : p∈P) (hq : q∈P) (hd : d∈pairBand rho p q) :
    p∈slabPoints P rho d (slabCode rho d p) ∧
      q∈slabPoints P rho d (slabCode rho d p) := by
  have hl := (le_div_iff₀ hrho).mp (Int.floor_le (value rho d p/rho))
  have hu := (div_lt_iff₀ hrho).mp (Int.lt_floor_add_one (value rho d p/rho))
  have hres : |value rho d p-rho*(slabCode rho d p:ℝ)|≤rho := by
    unfold slabCode
    exact abs_le.mpr ⟨by nlinarith only [hl,hrho],by nlinarith only [hu]⟩
  have hband := (Finset.mem_filter.mp hd).2
  have htri := abs_add_le (value rho d q-value rho d p)
    (value rho d p-rho*(slabCode rho d p:ℝ))
  have he : value rho d q-value rho d p+(value rho d p-rho*(slabCode rho d p:ℝ))=
      value rho d q-rho*(slabCode rho d p:ℝ) := by ring
  rw [he] at htri
  exact ⟨Finset.mem_filter.mpr ⟨hp,by linarith only [hres,hrho]⟩,
    Finset.mem_filter.mpr ⟨hq,by linarith only [htri,hband,hres]⟩⟩

/-- Fixing the first ORIGINAL point, every nonheavy band partner lies in
one actual light slab. This proves the per-direction bad-pair estimate from
literal populations, without assuming a row cap. -/
theorem original_nonheavy_partner_bound (P : Finset Point3) (rho H : ℝ)
    (d : DirectionLabel) (p : Point3) (hrho : 0<rho) (hH : 0≤H) (hp : p∈P) :
    ((nonheavyPartners P rho H d p).card : ℝ)≤H := by
  by_cases hn : (nonheavyPartners P rho H d p).Nonempty
  · obtain ⟨q,hq⟩ := hn
    obtain ⟨hqP,hqband,hqbad⟩ := Finset.mem_filter.mp hq
    have hboth := own_slab_contains_band P rho d p q hrho hp hqP hqband
    have hlight : ((slabPoints P rho d (slabCode rho d p)).card : ℝ)<H := by
      by_contra hnot
      exact hqbad ⟨slabCode rho d p,Finset.mem_image.mpr ⟨p,hp,rfl⟩,
        le_of_not_gt hnot,hboth⟩
    have hsub : nonheavyPartners P rho H d p⊆slabPoints P rho d (slabCode rho d p) := by
      intro v hv
      obtain ⟨hvP,hvband,_hvbad⟩ := Finset.mem_filter.mp hv
      exact (own_slab_contains_band P rho d p v hrho hp hvP hvband).2
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hlight.le
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.card_empty,Nat.cast_zero]
    exact hH

def badDirectionPairs (G : Finset Pair3) (P : Finset Point3) (rho H : ℝ)
    (d : DirectionLabel) : Finset Pair3 :=
  G.filter (fun z => d∈pairBand rho z.1 z.2 ∧ ¬heavyWitness P rho H d z)

/-- The per-direction count retains the ORIGINAL ordered pair labels. -/
theorem original_nonheavy_pair_bound (P : Finset Point3) (G : Finset Pair3)
    (rho H : ℝ) (d : DirectionLabel) (hrho : 0<rho) (hH : 0≤H)
    (hG : G⊆P.product P) :
    ((badDirectionPairs G P rho H d).card : ℝ)≤P.card*H := by
  have hsub : badDirectionPairs G P rho H d⊆
      P.biUnion (fun p => ({p}:Finset Point3).product (nonheavyPartners P rho H d p)) := by
    intro z hz
    obtain ⟨hzG,hband,hbad⟩ := Finset.mem_filter.mp hz
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp (hG hzG)
    exact Finset.mem_biUnion.mpr ⟨z.1,hp,Finset.mem_product.mpr
      ⟨Finset.mem_singleton_self _,Finset.mem_filter.mpr ⟨hq,hband,hbad⟩⟩⟩
  have hcount := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  have hcount' : ((badDirectionPairs G P rho H d).card : ℝ)≤
      ∑ p∈P, ((nonheavyPartners P rho H d p).card : ℝ) := by
    simpa only [Finset.product_eq_sprod,Finset.card_product,Finset.card_singleton,one_mul,Nat.cast_sum]
      using (show ((badDirectionPairs G P rho H d).card : ℝ)≤
        (∑ p∈P, (({p}:Finset Point3).product (nonheavyPartners P rho H d p)).card : ℕ) by
          exact_mod_cast hcount)
  calc
    _ ≤ ∑ p∈P, ((nonheavyPartners P rho H d p).card : ℝ) := hcount'
    _ ≤ ∑ _p∈P, H := Finset.sum_le_sum (fun p hp => original_nonheavy_partner_bound P rho H d p hrho hH hp)
    _ = _ := by simp

end OriginalThreeDimensionalHeavySlabs
