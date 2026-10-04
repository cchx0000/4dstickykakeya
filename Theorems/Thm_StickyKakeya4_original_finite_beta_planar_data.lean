import Theorems.Thm_StickyKakeya4_original_finite_beta_power_transport
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4800000

noncomputable section
namespace OriginalFiniteBetaPlanarData
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalLiteralSlabCover OriginalThreeDimensionalVoronoiFibers
open OriginalProjectedOwnerProfile OriginalNormalizedOwnerGraph OriginalNormalizedOwnerQuery
open OriginalFiniteBetaGrid OriginalFiniteBetaPowerTransport OriginalUnweightedSlicePowerData

/-- Actual original owner points and edges, with fixed per-bin A1
parameters. Both the graph mass and rich witness have strict slack. -/
def OwnerBinData (G : Finset Pair3) (b : Frame3) (C : Finset Point3) (hC : C.Nonempty)
    (mu W theta zeta epsilon chi : ℝ) (i : ℕ) : Prop :=
  let X := normalizedImage b C
  let J := normalizedOwnerGraph b G C hC
  X.Nonempty ∧ (∀ x∈X,|x.1| ≤ 1 ∧ |x.2| ≤ 1) ∧
    (∀ x∈X,∀ y∈X,x≠y → mu ≤ PlanarFrostmanBallConversion.euclideanDistance x y) ∧
    (∀ a : ℝ×ℝ,∀ R : ℝ,mu ≤ R →
      ((X.filter (fun x => PlanarFrostmanBallConversion.euclideanDistance a x ≤ R)).card : ℝ) ≤
        mu^(-theta)*R*X.card) ∧
    J⊆X.product X ∧ J.Nonempty ∧ mu^(theta/2)*(X.card : ℝ)^2 < J.card ∧
    ∀ e∈J,e.1≠e.2 ∧
      (∃ z∈G,normalizedPair b (originalOwner C hC z.1) (originalOwner C hC z.2)=e) ∧
      mu^(-binGain zeta i)*W*X.card < (OriginalPhysicalPairTube.physicalPairTube X W e).card ∧
      ((OriginalPhysicalPairTube.physicalPairTube X (mu^(binCapExponent zeta epsilon i)) e).card : ℝ) ≤
        mu^chi*X.card

/-- A chosen literal beta bin transports the constructed power data at
its unchanged physical fine mesh and unchanged owner query width. -/
theorem original_owner_power_to_beta_bin (G : Finset Pair3) (b : Frame3)
    (C : Finset Point3) (hC : C.Nonempty) (delta Delta r eta zeta epsilon e2 : ℝ) (i : ℕ)
    (hd : 0 < delta) (hd1 : delta < 1) (hDelta : 0 < Delta) (hr : 0 < r)
    (heta : 0 < eta) (hzeta : 0 < zeta) (hepsilon : 0 < epsilon) (he2 : 0 < e2)
    (hlower : delta ≤ Delta/32) (hupper : Delta/32 ≤ delta^(zeta/5))
    (hbinLower : binLower zeta i ≤ meshBeta delta (Delta/32))
    (hbinUpper : meshBeta delta (Delta/32) ≤ binUpper zeta i)
    (hcut : delta^((51/1000:ℝ)*epsilon) ≤ 1/16)
    (hdata : OwnerPowerData G b C hC delta Delta r eta zeta (delta^((51/50:ℝ)*epsilon)) e2) :
    OwnerBinData G b C hC (Delta/32) (50*Delta/r) (200*eta/zeta) zeta epsilon (zeta*e2/20) i := by
  obtain ⟨hmu,_hmu1,_hbetaLo,_hbetaHi,hmesh⟩ := original_mesh_beta_spec delta (Delta/32) zeta
    hd hd1 hzeta hlower hupper
  obtain ⟨hprofilePower,hgraphPower⟩ := original_beta_regularity_powers delta (Delta/32) zeta eta
    hd hd1 hzeta heta hlower hupper
  have hgain := (original_beta_bin_strict_gain delta (Delta/32) zeta (meshBeta delta (Delta/32)) i
    hd hd1 hzeta hmesh hbinUpper).2
  have hradius := original_beta_bin_cap_radius delta (Delta/32) zeta epsilon (meshBeta delta (Delta/32)) i
    hd hd1.le hzeta hepsilon hmesh hbinLower hcut
  obtain ⟨hX,hbox,hsep,hprofile,hJG,hJ,hmass,hedges⟩ := hdata
  have hN : (0:ℝ) < (normalizedImage b C).card := by exact_mod_cast hX.card_pos
  have hW : 0 < 50*Delta/r := by positivity
  refine ⟨hX,hbox,hsep,?_,hJG,hJ,?_,?_⟩
  · intro a R hR
    have hR0 : 0 ≤ R := hmu.le.trans hR
    exact (hprofile a R hR).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprofilePower hR0) hN.le)
  · exact (mul_lt_mul_of_pos_right hgraphPower (sq_pos_of_pos hN)).trans_le hmass
  · intro e he
    obtain ⟨hne,hwitness,hrich,hcap⟩ := hedges e he
    refine ⟨hne,hwitness,?_,?_⟩
    · exact (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hgain hW) hN).trans_le hrich
    · have hsub : OriginalPhysicalPairTube.physicalPairTube (normalizedImage b C)
          ((Delta/32)^(binCapExponent zeta epsilon i)) e⊆
          OriginalPhysicalPairTube.physicalPairTube (normalizedImage b C)
            (delta^((51/50:ℝ)*epsilon)/16) e := by
        intro x hx
        obtain ⟨hxX,t,ht⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨hxX,t,ht.trans hradius⟩
      exact ((Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hcap).trans
        (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hd.le hlower (by positivity)) hN.le)

end OriginalFiniteBetaPlanarData
