import Theorems.Thm_StickyKakeya4_native_original_bad_radius_source
import Theorems.Thm_StickyKakeya4_original_three_dimensional_good_radius_graph
import Theorems.Thm_StickyKakeya4_native_original_e2_first_beta_planar_slice
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7200000

noncomputable section
namespace NativeOriginalAllRadiusPlanarReduction
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalGridUniformity
open OriginalPhysicalTubeScaleSelection OriginalThreeDimensionalLiteralSlabCover
open OriginalThreeDimensionalBadRadiusSelection OriginalThreeDimensionalGoodRadiusGraph
open NativeOriginalBadRadiusSource NativeOriginalE2FirstBetaPlanarSlice
open OriginalFiniteBetaGrid OriginalFiniteBetaPlanarData

/-- Literal source accounting and fixed-bin planar data constructed from
an actual all-radius original bad-pair graph. This is only an output. -/
def OriginalAllRadiusPlanarWitness (P : Finset Point3)
    (delta eta zeta epsilon e2 : ℝ) (N : ℕ) : Prop :=
  ∃ n j : ℕ,delta ≤ dyadicRadius n ∧ dyadicRadius n ≤ 2*delta ∧ j ≤ n ∧
    delta ≤ dyadicRadius j ∧ dyadicRadius j ≤ 1 ∧
    ∃ H : Finset Pair3,H⊆farPairs (badPairs P delta zeta) (delta^(2*eta)) ∧
      H⊆P.product P ∧ H.Nonempty ∧
      ((badPairs P delta zeta).card : ℝ) ≤ ((n:ℝ)+1)*H.card+delta^(3*eta)*(P.card : ℝ)^2 ∧
      delta^eta*(P.card : ℝ)^2 ≤ H.card ∧
      (∀ z∈H,delta^(2*eta) ≤ distance3 z.1 z.2) ∧
      (∀ z∈H,delta^(-(zeta-zeta/100))*(dyadicRadius j)^(2-zeta/100)*P.card ≤
        4*(physicalPairTube3 P (dyadicRadius j) z).card) ∧
      let r := delta^(2*eta)
      let Delta := 54*(dyadicRadius j)/r
      let mu := Delta/32
      let W := 50*Delta/r
      let q := delta^((51/50:ℝ)*epsilon)
      delta ≤ mu ∧ mu ≤ delta^(zeta/5) ∧ mu ≤ W ∧ W ≤ q/32 ∧
      ∃ i : ℕ,i ≤ N ∧ binLower zeta i ≤ meshBeta delta mu ∧ meshBeta delta mu ≤ binUpper zeta i ∧
      ∃ b : Frame3,∃ C : Finset Point3,∃ hC : C.Nonempty,∃ G' : Finset Pair3,
        C⊆P ∧ G'⊆H ∧ OwnerBinData G' b C hC mu W (200*eta/zeta) zeta epsilon (zeta*e2/20) i

/-- Primitive original separated/grid-uniform/two-Frostman and literal
finite-slab input gives either the desired simultaneous all-radius good
graph or a fully constructed fixed-bin planar counterexample candidate.
No common physical radius, dense graph, selected slice, or planar gain
certificate is assumed. E2 precedes the arbitrary functional allowance. -/
theorem exists_original_all_radius_planar_reduction (zeta epsilon eps2 : ℝ)
    (hzeta : 0 < zeta) (hzeta1 : zeta < 1) (hepsilon : 0 < epsilon)
    (hepsmall : epsilon ≤ zeta/100) (heps2 : 0 < eps2) :
    ∃ N : ℕ,
      (∀ i : ℕ,i ≤ N → 0 < binGain zeta i ∧ binGain zeta i ≤ 10/19 ∧
        0 < binCapExponent zeta epsilon i ∧ binCapExponent zeta epsilon i ≤ binGain zeta i/8 ∧
        0 ≤ 1-binGain zeta i/2 ∧ 1-binGain zeta i/2 < 1) ∧
      ∃ e2 : ℝ,0 < e2 ∧ 200*e2 ≤ epsilon ∧
      ∀ etaUpper : ℝ,0 < etaUpper →
      ∃ eta : ℝ,0 < eta ∧ eta ≤ etaUpper ∧ eta ≤ zeta/1000 ∧ eta ≤ zeta*e2/10000 ∧
      ∃ delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1/2 ∧
      ∀ etaSource : ℝ,0 < etaSource → etaSource ≤ eta →
      ∀ delta : ℝ,0 < delta → delta ≤ delta0 →
      ∀ P : Finset Point3,
        (∀ p∈P,∀ j,|p j| ≤ 1) →
        (∀ p∈P,∀ x∈P,p≠x → delta ≤ distance3 p x) →
        OriginalGridUniform P delta (delta^(-etaSource)) →
        (∀ p∈P,∀ R : ℝ,delta ≤ R → R ≤ 1 →
          ((P.filter (fun x => distance3 p x ≤ R)).card : ℝ) ≤ delta^(-etaSource)*R^2*P.card) →
        (∀ b : Frame3,∀ c : ℝ,∀ k : ℤ×ℤ,
          ((P.filter (fun x => x∈rectangle b c (delta^epsilon/2) k)).card : ℝ) ≤ delta^eps2*P.card) →
        HasOriginalAllRadiusGraph P delta zeta (delta^(etaSource/10)) ∨
          OriginalAllRadiusPlanarWitness P delta eta zeta epsilon e2 N := by
  obtain ⟨N,hmenu,e2,he2,he2small,hPlanar⟩ := exists_native_original_e2_first_beta_planar_threshold
    zeta 4 epsilon eps2 hzeta hzeta1 (by norm_num) hepsilon hepsmall heps2
  refine ⟨N,hmenu,e2,he2,he2small,?_⟩
  intro etaUpper hupper
  obtain ⟨eta,heta,hetaUpper,hetaFine,hetaCap,dS,hdS,hdS1,hS⟩ := hPlanar etaUpper hupper
  have hetaHalf : 2*eta ≤ 1 := by linarith only [hetaFine,hzeta1]
  obtain ⟨dB,hdB,_hdB1,hB⟩ := exists_original_bad_radius_source_cutoff zeta eta hzeta heta hetaHalf
  refine ⟨eta,heta,hetaUpper,hetaFine,hetaCap,min dS dB,lt_min hdS hdB,(min_le_left _ _).trans hdS1,?_⟩
  intro etaSource hetaSource hetaLe delta hd hsmall P hbox hseparated huniform hfrostman hrect
  have hsmallS := hsmall.trans (min_le_left _ _)
  have hsmallB := hsmall.trans (min_le_right _ _)
  have hd1 : delta ≤ 1 := (hsmallS.trans hdS1).trans (by norm_num)
  by_cases hP : P.Nonempty
  swap
  · left
    apply original_good_graph_from_small_bad
    have hPe : P=∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    simp [hPe,badPairs,Finset.product_eq_sprod]
  rcases hB etaSource hetaSource hetaLe delta hd hsmallB P hP hfrostman with hsmallBad|hlarge
  · exact Or.inl (original_good_graph_from_small_bad P delta zeta (delta^(etaSource/10)) hsmallBad)
  right
  obtain ⟨n,j,hmesh,hbottom,hjn,hquery,hrho1,H,hHF,hHP,hH,hsepH,hretain,hdenseH,hgainH⟩ := hlarge
  have hcoefficient : delta^(-etaSource) ≤ delta^(-eta) :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith only [hetaLe])
  have huniformI : OriginalGridUniform P delta (delta^(-eta)) := by
    intro a ha b hb R hR hR1
    exact (huniform a ha b hb R hR hR1).trans
      (mul_le_mul_of_nonneg_right hcoefficient (Nat.cast_nonneg _))
  have hfrostmanI (p : Point3) (hp : p∈P) (R : ℝ) (hR : delta ≤ R) (hR1 : R ≤ 1) :
      ((P.filter (fun x => distance3 p x ≤ R)).card : ℝ) ≤ delta^(-eta)*R^2*P.card :=
    (hfrostman p hp R hR hR1).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg R)) (Nat.cast_nonneg _))
  have hdata := hS eta heta le_rfl delta hd hsmallS P H (dyadicRadius j) j hP hquery hrho1 rfl hHP
    hbox hseparated huniformI hsepH hdenseH hfrostmanI hgainH hrect
  exact ⟨n,j,hmesh,hbottom,hjn,hquery,hrho1,H,hHF,hHP,hH,hretain,hdenseH,hsepH,hgainH,hdata⟩

end NativeOriginalAllRadiusPlanarReduction
