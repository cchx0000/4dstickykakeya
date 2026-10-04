import Theorems.Thm_StickyKakeya4_original_three_dimensional_bad_radius_selection
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5600000

noncomputable section
namespace NativeOriginalBadRadiusSource
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalBadRadiusSelection
open OriginalPhysicalTubeScaleSelection NativeRadialDensestGraph
open OriginalThreeDimensionalSliceParameterChoice NativeQuarterScaleParameters

/-- One cutoff, fixed before the external source exponent, turns a large
literal all-radius bad graph into the actual common-rho input. Only the
original near-diagonal count and one original dyadic menu are charged. -/
theorem exists_original_bad_radius_source_cutoff (zeta eta : ℝ)
    (hzeta : 0 < zeta) (heta : 0 < eta) (hetaHalf : 2*eta ≤ 1) :
    ∃ delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1/2 ∧
      ∀ etaSource : ℝ,0 < etaSource → etaSource ≤ eta →
      ∀ delta : ℝ,0 < delta → delta ≤ delta0 →
      ∀ P : Finset Point3,P.Nonempty →
        (∀ p∈P,∀ R : ℝ,delta ≤ R → R ≤ 1 →
          ((P.filter (fun x => distance3 p x ≤ R)).card : ℝ) ≤ delta^(-etaSource)*R^2*P.card) →
        ((badPairs P delta zeta).card : ℝ) ≤ delta^(etaSource/10)*(P.card : ℝ)^2 ∨
        ∃ n j : ℕ,delta ≤ dyadicRadius n ∧ dyadicRadius n ≤ 2*delta ∧ j ≤ n ∧
          delta ≤ dyadicRadius j ∧ dyadicRadius j ≤ 1 ∧
          ∃ H : Finset Pair3,H⊆farPairs (badPairs P delta zeta) (delta^(2*eta)) ∧
            H⊆P.product P ∧ H.Nonempty ∧
            (∀ z∈H,delta^(2*eta) ≤ distance3 z.1 z.2) ∧
            ((badPairs P delta zeta).card : ℝ) ≤ ((n:ℝ)+1)*H.card+delta^(3*eta)*(P.card : ℝ)^2 ∧
            delta^eta*(P.card : ℝ)^2 ≤ H.card ∧
            ∀ z∈H,delta^(-(zeta-zeta/100))*(dyadicRadius j)^(2-zeta/100)*P.card ≤
              4*(physicalPairTube3 P (dyadicRadius j) z).card := by
  obtain ⟨dM,hdM,_hdM1,hM⟩ := exists_original_coarse_menu_cutoff (eta/4) (by positivity)
  obtain ⟨dC,hdC,_hdC1,hC⟩ := exists_small_power_cutoff
    (show 0 < 13*eta/20 by positivity) (by norm_num : (0:ℝ) < 1/2)
  refine ⟨min (1/2) (min dM dC),lt_min (by norm_num) (lt_min hdM hdC),min_le_left _ _,?_⟩
  intro etaSource _hetaSource hetaLe delta hd hsmall P _hP hfrostman
  have hd1 : delta ≤ 1 := (hsmall.trans (min_le_left _ _)).trans (by norm_num)
  have hsmallM := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallC := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  by_cases hsmallBad : ((badPairs P delta zeta).card : ℝ) ≤ delta^(etaSource/10)*(P.card : ℝ)^2
  · exact Or.inl hsmallBad
  right
  have hlarge : delta^(etaSource/10)*(P.card : ℝ)^2 < (badPairs P delta zeta).card := lt_of_not_ge hsmallBad
  have hlargeI : delta^(eta/10)*(P.card : ℝ)^2 < (badPairs P delta zeta).card :=
    (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith only [hetaLe]))
      (sq_nonneg (P.card : ℝ))).trans_lt hlarge
  let r := delta^(2*eta)
  let F := farPairs (badPairs P delta zeta) r
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := Real.rpow_le_one hd.le hd1 (by positivity)
  have hdr : delta ≤ r := by
    have hh := Real.rpow_le_rpow_of_exponent_ge hd hd1 hetaHalf
    simpa only [Real.rpow_one] using hh
  have hcoefficient : delta^(-etaSource) ≤ delta^(-eta) :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith only [hetaLe])
  have hfr (p : Point3) (hp : p∈P) (R : ℝ) (hR : delta ≤ R) (hR1 : R ≤ 1) :
      ((P.filter (fun x => distance3 p x ≤ R)).card : ℝ) ≤ delta^(-eta)*R^2*P.card :=
    (hfrostman p hp R hR hR1).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg R)) (Nat.cast_nonneg _))
  have hnear := original_off_diagonal_pair_loss P (badPairs P delta zeta) delta (delta^(-eta)) r hdr hr1
    (Finset.filter_subset _ _) hfr
  have hidentity : delta^(-eta)*r^2=delta^(3*eta) := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast hd.le,← Real.rpow_add hd]
    congr 1
    ring
  rw [hidentity] at hnear
  have hnearSmall : delta^(3*eta) ≤ delta^(eta/10) :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith only [heta])
  have hFpos : (0:ℝ) < F.card := by
    have hh := mul_le_mul_of_nonneg_right hnearSmall (sq_nonneg (P.card : ℝ))
    change ((badPairs P delta zeta).card : ℝ) ≤ F.card+delta^(3*eta)*(P.card : ℝ)^2 at hnear
    linarith only [hnear,hh,hlargeI]
  have hF : F.Nonempty := Finset.card_pos.mp (by exact_mod_cast hFpos)
  have hFP : F⊆P.product P := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hbad (z : Pair3) (hz : z∈F) : ∃ R : ℝ,delta ≤ R ∧ R ≤ 1 ∧
      delta^(-zeta)*R^2*P.card ≤ (physicalPairTube3 P R z).card := by
    obtain ⟨R,hR,hR1,hpop⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
    exact ⟨R,hR,hR1,hpop.le⟩
  obtain ⟨n,hmesh,hbottom⟩ := exists_original_dyadic_mesh delta hd hd1
  obtain ⟨j,hjn,hdrho,hrho1,H,hHF,hHP,hH,hcount,hgain⟩ := exists_original_bad_graph_dyadic_source
    P F delta zeta (zeta/100) n hd (by positivity) hbottom hF hFP hbad
  have hretain : ((badPairs P delta zeta).card : ℝ) ≤
      ((n:ℝ)+1)*H.card+delta^(3*eta)*(P.card : ℝ)^2 := by
    linarith only [hnear,hcount]
  have hmenu := hM delta hd hsmallM n hmesh
  have hmenuPower : ((n:ℝ)+1)*delta^eta ≤ delta^(3*eta/4) := by
    have hh := mul_le_mul_of_nonneg_right hmenu (Real.rpow_nonneg hd.le eta)
    have he : delta^(-(eta/4))*delta^eta=delta^(3*eta/4) := by
      rw [← Real.rpow_add hd]
      congr 1
      ring
    exact hh.trans_eq he
  have hsmallPower : 2*delta^(3*eta/4) ≤ delta^(eta/10) := by
    have hh := mul_le_mul_of_nonneg_right (hC delta hd hsmallC) (Real.rpow_nonneg hd.le (eta/10))
    have he : delta^(13*eta/20)*delta^(eta/10)=delta^(3*eta/4) := by
      rw [← Real.rpow_add hd]
      congr 1
      ring
    rw [he] at hh
    linarith only [hh]
  have hscalar : delta^(3*eta)+((n:ℝ)+1)*delta^eta ≤ delta^(eta/10) := by
    have hn := Real.rpow_le_rpow_of_exponent_ge hd hd1 (show 3*eta/4 ≤ 3*eta by linarith only [heta])
    linarith only [hn,hmenuPower,hsmallPower]
  have hdense : delta^eta*(P.card : ℝ)^2 ≤ H.card := by
    by_contra hnot
    have hh := mul_lt_mul_of_pos_left (lt_of_not_ge hnot) (show 0 < (n:ℝ)+1 by positivity)
    have hc := mul_le_mul_of_nonneg_right hscalar (sq_nonneg (P.card : ℝ))
    nlinarith only [hh,hc,hretain,hlargeI]
  refine ⟨n,j,hmesh,hbottom,hjn,hdrho,hrho1,H,hHF,hHP,hH,?_,hretain,hdense,hgain⟩
  intro z hz
  exact (Finset.mem_filter.mp (hHF hz)).2

end NativeOriginalBadRadiusSource
