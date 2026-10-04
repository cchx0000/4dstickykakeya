import Theorems.Thm_StickyKakeya4_original_three_dimensional_chosen_slice_tube
import Theorems.Thm_StickyKakeya4_native_radial_densest_graph
import Mathlib.Combinatorics.Pigeonhole

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4800000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalBadRadiusSelection
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalSliceMaximizer
open OriginalPhysicalTubeScaleSelection NativeRadialDensestGraph

/-- Literal failure of the desired all-radius original pair-tube bound. -/
def badPairs (P : Finset Point3) (delta zeta : ℝ) : Finset Pair3 :=
  (P.product P).filter (fun z => ∃ R : ℝ,delta ≤ R ∧ R ≤ 1 ∧
    delta^(-zeta)*R^2*P.card < (physicalPairTube3 P R z).card)

def farPairs (G : Finset Pair3) (r : ℝ) : Finset Pair3 :=
  G.filter (fun z => r ≤ distance3 z.1 z.2)

/-- The exact original two-Frostman profile pays the full ordered-pair
loss at the chosen legal off-diagonal radius. -/
theorem original_off_diagonal_pair_loss (P : Finset Point3) (G : Finset Pair3)
    (delta K r : ℝ) (hquery : delta ≤ r) (hr1 : r ≤ 1) (hGP : G⊆P.product P)
    (hfrostman : ∀ p∈P,∀ R : ℝ,delta ≤ R → R ≤ 1 →
      ((P.filter (fun x => distance3 p x ≤ R)).card : ℝ) ≤ K*R^2*P.card) :
    (G.card : ℝ) ≤ (farPairs G r).card+K*r^2*(P.card : ℝ)^2 := by
  let B := (P.product P).filter (fun z => distance3 z.1 z.2 < r)
  have hrow (p : Point3) (hp : p∈P) :
      ((P.filter (fun x => distance3 p x < r)).card : ℝ) ≤ K*r^2*P.card := by
    have hsub : P.filter (fun x => distance3 p x < r)⊆P.filter (fun x => distance3 p x ≤ r) := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2.le⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hfrostman p hp r hquery hr1)
  have hcount : B.card=∑ p∈P,(P.filter (fun x => distance3 p x < r)).card := by
    simp only [B,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]
  have hcountR : (B.card : ℝ)=∑ p∈P,((P.filter (fun x => distance3 p x < r)).card : ℝ) := by
    exact_mod_cast hcount
  have hB : (B.card : ℝ) ≤ K*r^2*(P.card : ℝ)^2 := by
    rw [hcountR]
    calc
      _ ≤ ∑ _p∈P,K*r^2*(P.card : ℝ) := Finset.sum_le_sum hrow
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  have hcover : G⊆farPairs G r∪B := by
    intro z hz
    by_cases hsep : r ≤ distance3 z.1 z.2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz,hsep⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hGP hz,lt_of_not_ge hsep⟩)
  have hcard : (G.card : ℝ) ≤ (farPairs G r).card+B.card := by
    exact_mod_cast (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  linarith only [hcard,hB]

/-- Rounding an actual bad physical radius costs only four. The native
source gain follows directly, with no maximizing scale or occupancy bin. -/
theorem original_bad_radius_has_dyadic_gain (P : Finset Point3) (z : Pair3)
    (delta zeta gamma : ℝ) (n : ℕ) (hd : 0 < delta) (hgamma : 0 ≤ gamma)
    (hbottom : dyadicRadius n ≤ 2*delta)
    (hbad : ∃ R : ℝ,delta ≤ R ∧ R ≤ 1 ∧
      delta^(-zeta)*R^2*P.card ≤ (physicalPairTube3 P R z).card) :
    ∃ j : ℕ,j ≤ n ∧ delta ≤ dyadicRadius j ∧ dyadicRadius j ≤ 1 ∧
      delta^(-(zeta-gamma))*(dyadicRadius j)^(2-gamma)*P.card ≤
        4*(physicalPairTube3 P (dyadicRadius j) z).card := by
  obtain ⟨R,hRlo,hRhi,hpop⟩ := hbad
  have hR : 0 < R := hd.trans_le hRlo
  obtain ⟨j,hjn,hRrho,hrhoR⟩ := dyadic_radius_cover n R
    (hbottom.trans (mul_le_mul_of_nonneg_left hRlo (by norm_num))) hRhi
  let rho := dyadicRadius j
  have hrho : 0 < rho := hR.trans_le hRrho
  have hdrho : delta ≤ rho := hRlo.trans hRrho
  have hrho1 : rho ≤ 1 := pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  have hpopRho := hpop.trans (Nat.cast_le.mpr (Finset.card_le_card (original_physical_tube3_mono P z hRrho)))
  have hsquare := pow_le_pow_left₀ hrho.le hrhoR 2
  have hmass := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsquare (Real.rpow_nonneg hd.le (-zeta))) (Nat.cast_nonneg P.card)
  have hgainBase : delta^(-zeta)*rho^2*P.card ≤ 4*(physicalPairTube3 P rho z).card := by
    nlinarith only [hmass,hpopRho]
  have hpower := Real.rpow_le_rpow hd.le hdrho hgamma
  have hdPower : delta^(-(zeta-gamma))=delta^(-zeta)*delta^gamma := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  have hrhoPower : rho^gamma*rho^(2-gamma)=rho^2 := by
    rw [← Real.rpow_add hrho,show gamma+(2-gamma)=2 by ring,Real.rpow_two]
  have hgain : delta^(-(zeta-gamma))*rho^(2-gamma)*P.card ≤ delta^(-zeta)*rho^2*P.card := by
    rw [hdPower]
    calc
      _ ≤ (delta^(-zeta)*rho^gamma)*rho^(2-gamma)*P.card :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpower (Real.rpow_nonneg hd.le (-zeta)))
            (Real.rpow_nonneg hrho.le (2-gamma))) (Nat.cast_nonneg P.card)
      _ = _ := by rw [mul_assoc (delta^(-zeta)),hrhoPower]
  exact ⟨j,hjn,hdrho,hrho1,hgain.trans hgainBase⟩

/-- One genuine finite scale fiber of the original violating graph is
large. The only selection loss is the original dyadic menu length. -/
theorem exists_original_bad_graph_dyadic_source (P : Finset Point3) (G : Finset Pair3)
    (delta zeta gamma : ℝ) (n : ℕ) (hd : 0 < delta) (hgamma : 0 ≤ gamma)
    (hbottom : dyadicRadius n ≤ 2*delta) (hG : G.Nonempty) (hGP : G⊆P.product P)
    (hbad : ∀ z∈G,∃ R : ℝ,delta ≤ R ∧ R ≤ 1 ∧
      delta^(-zeta)*R^2*P.card ≤ (physicalPairTube3 P R z).card) :
    ∃ j : ℕ,j ≤ n ∧ delta ≤ dyadicRadius j ∧ dyadicRadius j ≤ 1 ∧
      ∃ H : Finset Pair3,H⊆G ∧ H⊆P.product P ∧ H.Nonempty ∧
        (G.card : ℝ) ≤ ((n:ℝ)+1)*H.card ∧
        ∀ z∈H,delta^(-(zeta-gamma))*(dyadicRadius j)^(2-gamma)*P.card ≤
          4*(physicalPairTube3 P (dyadicRadius j) z).card := by
  have hchoose : ∀ z : Pair3,∃ j : ℕ,z∈G → j ≤ n ∧ delta ≤ dyadicRadius j ∧
      dyadicRadius j ≤ 1 ∧ delta^(-(zeta-gamma))*(dyadicRadius j)^(2-gamma)*P.card ≤
        4*(physicalPairTube3 P (dyadicRadius j) z).card := by
    intro z
    by_cases hz : z∈G
    · obtain ⟨j,hj⟩ := original_bad_radius_has_dyadic_gain P z delta zeta gamma n hd hgamma hbottom (hbad z hz)
      exact ⟨j,fun _ => hj⟩
    · exact ⟨0,fun hz' => (hz hz').elim⟩
  choose index hindex using hchoose
  have hmap : ∀ z∈G,index z∈Finset.range (n+1) := by
    intro z hz
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hindex z hz).1)
  have hn : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hpigeon : (Finset.range (n+1)).card • ((G.card : ℝ)/((n:ℝ)+1)) ≤ (G.card : ℝ) := by
    simp only [Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
    rw [mul_div_cancel₀ _ (ne_of_gt hn)]
  obtain ⟨j,hj,hfiber⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    hmap ⟨0,Finset.mem_range.mpr (by omega)⟩ hpigeon
  let H := G.filter (fun z => index z=j)
  have hmass : (G.card : ℝ) ≤ ((n:ℝ)+1)*H.card := by
    have hh := (div_le_iff₀ hn).mp hfiber
    simpa only [mul_comm] using hh
  have hH : H.Nonempty := by
    have hgc : (0:ℝ) < G.card := by exact_mod_cast hG.card_pos
    have hhc : (0:ℝ) < H.card := (div_pos hgc hn).trans_le hfiber
    exact Finset.card_pos.mp (by exact_mod_cast hhc)
  have hgain (z : Pair3) (hz : z∈H) :
      delta ≤ dyadicRadius j ∧ dyadicRadius j ≤ 1 ∧
      delta^(-(zeta-gamma))*(dyadicRadius j)^(2-gamma)*P.card ≤
        4*(physicalPairTube3 P (dyadicRadius j) z).card := by
    obtain ⟨hzG,hidx⟩ := Finset.mem_filter.mp hz
    have hh := (hindex z hzG).2
    rwa [hidx] at hh
  obtain ⟨z0,hz0⟩ := hH
  exact ⟨j,by have hh := Finset.mem_range.mp hj; omega,(hgain z0 hz0).1,(hgain z0 hz0).2.1,
    H,Finset.filter_subset _ _,(Finset.filter_subset _ _).trans hGP,⟨z0,hz0⟩,hmass,
    fun z hz => (hgain z hz).2.2⟩

end OriginalThreeDimensionalBadRadiusSelection
