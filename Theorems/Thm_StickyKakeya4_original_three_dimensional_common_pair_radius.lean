import Theorems.Thm_StickyKakeya4_original_three_dimensional_common_slice_radius
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3600000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalCommonPairRadius
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalHeavySlabs OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalSliceMaximizer OriginalPhysicalTubeScaleSelection
open OriginalThreeDimensionalCommonSliceRadius

/-- Both radius selections are on actual original incidences. First select
whole direction fibers per original pair, then a whole original-pair fiber
with one common radius. The two n+1 losses are explicit, and no target
bound on a discarded graph or any hairbrush gain is assumed. -/
theorem exists_original_common_rich_pair_radius
    (P : Finset Point3) (G : Finset Pair3)
    (F : Pair3→Finset DirectionLabel) (k : Pair3→DirectionLabel→ℤ)
    (rho r eta1 e1 e2 b : ℝ) (n M : ℕ)
    (hrho : 0 < rho) (hr : 0 < r) (hr1 : r ≤ 1) (he1 : 0 < e1) (he11 : e1 ≤ 1)
    (he2 : 0 < e2) (halpha : 200*e2/e1 ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (hmesh : rho=dyadicRadius n) (hcontract : (dyadicRadius M)^(200*e2/e1) ≤ 1/2)
    (hDelta : 54*rho/r ≤ 1) (hG : G.Nonempty) (hGP : G⊆P.product P)
    (hbox : ∀ p∈P, ∀ i, |p i| ≤ 1) (hsep : ∀ z∈G, r ≤ distance3 z.1 z.2)
    (hFmass : ∀ z∈G, b ≤ rho*((F z).card : ℝ))
    (hband : ∀ z∈G, F z⊆pairBand rho z.1 z.2)
    (hslabs : ∀ z∈G, ∀ d∈F z, z.1∈slabPoints P rho d (k z d) ∧ z.2∈slabPoints P rho d (k z d))
    (hheavy : ∀ z∈G, ∀ d∈F z, rho^(1+eta1)*(P.card : ℝ) ≤ (slabPoints P rho d (k z d)).card)
    (hconc : ∀ z∈G, ∀ d∈F z, (54*rho/r)^e2*((enlargedSlice P rho d (k z d) (54*rho/r)).card : ℝ) ≤
      (physicalPairTube3 (enlargedSlice P rho d (k z d) (54*rho/r)) ((54*rho/r)^e1) z).card) :
    let D := 54*rho/r
    let alpha := 200*e2/e1
    let nu := b/((n:ℝ)+1)*(dyadicRadius M*r^2/4665600000*rho^eta1*D^(e2+alpha*(1-e1)))
    0 < nu ∧ ∃ j : ℕ, j ≤ n ∧ ∃ H : Finset Pair3,
      H⊆G ∧ H.Nonempty ∧ G.card ≤ (n+1)*H.card ∧
      ∀ z∈H, nu*dyadicRadius j*P.card ≤ (physicalPairTube3 P (dyadicRadius j) z).card ∧
        ∃ S : Finset DirectionLabel,
          S=(F z).filter (fun d => chosenSliceIndex P z (k z) rho D alpha n d=j) ∧
          S⊆F z ∧ S.Nonempty ∧ (F z).card ≤ (n+1)*S.card := by
  let D := 54*rho/r
  let alpha := 200*e2/e1
  let B := dyadicRadius M*r^2/4665600000*rho^eta1*D^(e2+alpha*(1-e1))
  let nu := b/((n:ℝ)+1)*B
  have hD : 0 < D := by dsimp [D]; positivity
  have hc : 0 < dyadicRadius M := by dsimp [dyadicRadius]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hN : 0 < (n:ℝ)+1 := by positivity
  have hN1 : 1 ≤ (n:ℝ)+1 := by
    have hh : (0:ℝ) ≤ n := by positivity
    linarith only [hh]
  have hnu : 0 < nu := by dsimp [nu]; positivity
  refine ⟨hnu,?_⟩
  have hchoose : ∀ z : Pair3, ∃ j : ℕ, ∃ S : Finset DirectionLabel, z∈G →
      j ≤ n ∧ S=(F z).filter (fun d => chosenSliceIndex P z (k z) rho D alpha n d=j) ∧
      S⊆F z ∧ S.Nonempty ∧ (F z).card ≤ (n+1)*S.card ∧
      nu*dyadicRadius j*P.card ≤ (physicalPairTube3 P (dyadicRadius j) z).card := by
    intro z
    by_cases hz : z∈G
    · have hF : (F z).Nonempty := by
        apply Finset.card_pos.mp
        by_contra hh
        have he : (F z).card=0 := by omega
        have hm := hFmass z hz
        rw [he,Nat.cast_zero,mul_zero] at hm
        exact (not_le_of_gt hb) hm
      obtain ⟨_hpositive,j,hj,S,hSeq,hSF,hSn,hmass,_hmax,hpop⟩ :=
        exists_original_concentrated_direction_radius P z (F z) (k z) rho r eta1 e1 e2 n M
          hrho hr hr1 he1 he11 he2 halpha hmesh hcontract hDelta hbox (hGP hz) (hsep z hz)
          hF (hband z hz) (hslabs z hz) (hheavy z hz) (hconc z hz)
      have hbeta : b/((n:ℝ)+1) ≤ min 1 (((F z).card : ℝ)*rho/(n+1)) := by
        apply le_min
        · exact (div_le_one hN).mpr (hb1.trans hN1)
        · have hh := div_le_div_of_nonneg_right (hFmass z hz) hN.le
          simpa only [mul_comm] using hh
      have htau : 0 < dyadicRadius j := by dsimp [dyadicRadius]; positivity
      have hcoef := mul_le_mul_of_nonneg_right hbeta hB.le
      have hcount := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef htau.le) (Nat.cast_nonneg P.card)
      refine ⟨j,S,fun _ => ⟨hj,hSeq,hSF,hSn,hmass,?_⟩⟩
      exact hcount.trans hpop
    · exact ⟨0,∅,fun hz' => (hz hz').elim⟩
  choose J W hJW using hchoose
  have hJ : ∀ z∈G, J z∈Finset.range (n+1) := by
    intro z hz
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hJW z hz).1)
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image (Finset.range (n+1))
    (fun i => (G.filter (fun z => J z=i)).card) ⟨0,Finset.mem_range.mpr (by omega)⟩
  let H := G.filter (fun z => J z=j)
  have hsum : ∑ i∈Finset.range (n+1), (G.filter (fun z => J z=i)).card=G.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    exact Finset.filter_eq_self.mpr hJ
  have hmass : G.card ≤ (n+1)*H.card := by
    calc
      _ = ∑ i∈Finset.range (n+1), (G.filter (fun z => J z=i)).card := hsum.symm
      _ ≤ ∑ _i∈Finset.range (n+1), H.card := Finset.sum_le_sum (fun i hi => hmax i hi)
      _ = _ := by simp
  have hH : H.Nonempty := by
    apply Finset.card_pos.mp
    have hg := hG.card_pos
    by_contra hh
    have hz : H.card=0 := by omega
    rw [hz,mul_zero] at hmass
    omega
  refine ⟨j,by have hh := Finset.mem_range.mp hj; omega,H,Finset.filter_subset _ _,hH,hmass,?_⟩
  intro z hz
  obtain ⟨hzG,hJz⟩ := Finset.mem_filter.mp hz
  obtain ⟨_hjz,hW,hWF,hWn,hWmass,hpop⟩ := hJW z hzG
  rw [hJz] at hW hpop
  exact ⟨hpop,W z,hW,hWF,hWn,hWmass⟩

end OriginalThreeDimensionalCommonPairRadius
