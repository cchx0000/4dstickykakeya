import Theorems.Thm_StickyKakeya4_original_normalized_owner_graph
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6200000

noncomputable section
open scoped BigOperators
namespace NativeOriginalUnweightedSliceFrame
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalLiteralSlabCover
open OriginalThreeDimensionalSlabProjection OriginalThreeDimensionalRawOwnerNet
open OriginalThreeDimensionalCoverBallUniformity OriginalThreeDimensionalGridUniformity
open OriginalThreeDimensionalUniformBallCover OriginalThreeDimensionalVoronoiFibers
open OriginalThreeDimensionalGridBalancedFibers OriginalThreeDimensionalAveragedSliceEnergy
open OriginalBalancedOwnerCounts OriginalFiniteCellWeights OriginalProjectedOwnerProfile
open OriginalThreeDimensionalOwnerGraphRichness OriginalNormalizedOwnerGraph
open OriginalNormalizedOwnerQuery OriginalNormalizedOwnerPhysicalBridge

/-- Literal output of the same-center construction. This is constructed
from original source data below and is never an input assumption. -/
def OriginalUnweightedSliceOutput (P Q S : Finset Point3) (G : Finset Pair3)
    (b : Frame3) (Delta r K K0 lam k qcap B : ℝ) : Prop :=
    let A := uniformFiberConstant K
    ∃ C : Finset Point3,∃ hC : C.Nonempty,∃ M : ℕ,
      C⊆S ∧ S⊆originalCarrier P C hC (Delta/4) ∧ originalCarrier P C hC (Delta/4)⊆Q ∧
      0 < M ∧ 1 ≤ A ∧
      (∀ p∈C,M ≤ (originalFiber P C hC (Delta/4) p).card ∧
        ((originalFiber P C hC (Delta/4) p).card : ℝ) ≤ A*M) ∧
      (∑ p∈C,(originalFiber P C hC (Delta/4) p).card)=(originalCarrier P C hC (Delta/4)).card ∧
      (normalizedImage b C).Nonempty ∧ (normalizedImage b C).card=C.card ∧
      (∀ p∈normalizedImage b C,|p.1| ≤ 1 ∧ |p.2| ≤ 1) ∧
      (∀ p∈normalizedImage b C,∀ q∈normalizedImage b C,p≠q →
        Delta/32 ≤ PlanarFrostmanBallConversion.euclideanDistance p q) ∧
      (∀ a : Point2,∀ R : ℝ,Delta/32 ≤ R →
        (((normalizedImage b C).filter (fun p => PlanarFrostmanBallConversion.euclideanDistance a p ≤ R)).card : ℝ) ≤
          (32*A*K0/lam)*R*(normalizedImage b C).card) ∧
      normalizedOwnerGraph b G C hC⊆(normalizedImage b C).product (normalizedImage b C) ∧
      (normalizedOwnerGraph b G C hC).Nonempty ∧
      lam*((normalizedImage b C).card : ℝ)^2 ≤ A^2*(normalizedOwnerGraph b G C hC).card ∧
      ∀ e∈normalizedOwnerGraph b G C hC,
        e.1≠e.2 ∧ (∃ z∈G,normalizedPair b (originalOwner C hC z.1) (originalOwner C hC z.2)=e) ∧
        k*(normalizedImage b C).card ≤ A*(OriginalPhysicalPairTube.physicalPairTube
          (normalizedImage b C) (50*Delta/r) e).card ∧
        ∀ R : ℝ,8*R+64*Delta/r ≤ qcap →
          lam*(OriginalPhysicalPairTube.physicalPairTube (normalizedImage b C) R e).card ≤
            A*B*(normalizedImage b C).card

/-- The SAME actual original raw-core net supplies all unweighted planar
fields. Full original grid uniformity constructs its fiber balance; actual
Q-potentials, original dense edges, original rich points and inherited pair
caps supply the remaining fields. No projected profile, chosen chart,
coarse source population or normalized cap is assumed. -/
theorem exists_original_unweighted_slice_frame (P Q S : Finset Point3)
    (G : Finset Pair3) (b : Frame3) (c delta rho Delta r K K0 lam k qcap B : ℝ)
    (hQ : Q=frameSlice P b c Delta) (hS : S.Nonempty) (hSP : S⊆P)
    (hd : 0 < delta) (hrho : 0 ≤ rho) (hDelta : 0 < Delta) (hr : 0 < r)
    (hquery : delta ≤ Delta/12) (hsmall : 32*Delta ≤ 1) (hDr : Delta ≤ r)
    (h54 : 54*rho/r ≤ Delta) (h48 : 48*rho ≤ Delta)
    (hK : 0 ≤ K) (hK0 : 0 ≤ K0) (hlam : 0 < lam) (hk : 0 ≤ k)
    (hqcap : qcap ≤ 1) (hB : 0 ≤ B)
    (hseparated : ∀ p∈P,∀ q∈P,p≠q → delta ≤ distance3 p q)
    (huniform : OriginalGridUniform P delta K)
    (hbox : ∀ p∈P,∀ j,|p j| ≤ 1)
    (hraw : ∀ p∈S,|frameCoordinate b 2 p-c| ≤ 3*rho)
    (hG : G⊆S.product S) (hsep : ∀ z∈G,r ≤ distance3 z.1 z.2)
    (hdense : lam*(Q.card : ℝ)^2 ≤ G.card)
    (hpotential : ∀ p∈S,slicePotential Q Delta p ≤ K0*Q.card)
    (hrich : ∀ z∈G,k*Q.card ≤ ((physicalPairTube3 S (32*Delta) z).card : ℝ))
    (hcap : ∀ z∈G,((physicalPairTube3 Q qcap z).card : ℝ) ≤ B*Q.card) :
    OriginalUnweightedSliceOutput P Q S G b Delta r K K0 lam k qcap B := by
  let A := uniformFiberConstant K
  obtain ⟨C,hC,hCS,hCP,hsepC,hnear,hSU,hUframe,_hprojected,_hinjP,_hcardP⟩ :=
    exists_original_raw_owner_net P S b c rho Delta hSP hS hDelta h48 hraw
  have hUQ : originalCarrier P C hC (Delta/4)⊆Q := by simpa only [hQ] using hUframe
  have hSQ : S⊆Q := hSU.trans hUQ
  have hCQ : C⊆Q := hCS.trans hSQ
  have hQP : Q⊆P := by rw [hQ]; exact Finset.filter_subset _ _
  have hQn : Q.Nonempty := hS.mono hSQ
  have hqc : (0:ℝ) < Q.card := by exact_mod_cast hQn.card_pos
  have hGU : G⊆(originalCarrier P C hC (Delta/4)).product (originalCarrier P C hC (Delta/4)) := by
    intro z hz
    obtain ⟨hz1,hz2⟩ := Finset.mem_product.mp (hG hz)
    exact Finset.mem_product.mpr ⟨hSU hz1,hSU hz2⟩
  have hGQ : G⊆Q.product Q := by
    intro z hz
    obtain ⟨hz1,hz2⟩ := Finset.mem_product.mp (hG hz)
    exact Finset.mem_product.mpr ⟨hSQ hz1,hSQ hz2⟩
  have hlam1 : lam ≤ 1 := by
    have hc : (G.card : ℝ) ≤ (Q.card : ℝ)^2 := by
      have hh := (Finset.card_le_card hGQ).trans_eq (Finset.card_product _ _)
      simpa only [Nat.cast_mul,pow_two] using (Nat.cast_le.mpr hh : (G.card : ℝ) ≤ (Q.card*Q.card : ℕ))
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hqc)).mp
    simpa only [one_mul] using hdense.trans hc
  have hcover := original_grid_uniform_implies_cover_uniform P delta K hd hK hseparated huniform
  obtain ⟨M,hM,hpop⟩ := exists_original_common_fiber_population P C hC delta
    ((packingConstant : ℝ)^2*K) (Delta/4) hd (by positivity) (by positivity)
    (by linarith only [hquery]) (by linarith only [hsmall,hDelta]) hCP hseparated hcover hsepC
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hmax (p : Point3) (hp : p∈C) :
      ((originalFiber P C hC (Delta/4) p).card : ℝ) ≤ A*M := by
    have he : (ballCoverConstant : ℝ)*(packingConstant : ℝ)*((packingConstant : ℝ)^2*K)*M=A*M := by
      dsimp [A,uniformFiberConstant]
      ring
    exact (hpop p hp).2.trans_eq he
  have hmin (p : Point3) (hp : p∈C) : (M:ℝ) ≤ (originalFiber P C hC (Delta/4) p).card :=
    Nat.cast_le.mpr (hpop p hp).1
  have hA1 : 1 ≤ A := by
    obtain ⟨p,hp⟩ := hC
    apply (mul_le_mul_iff_of_pos_right hMr).mp
    simpa only [one_mul] using (hmin p hp).trans (hmax p hp)
  have hA : 0 ≤ A := (by norm_num : (0:ℝ) ≤ 1).trans hA1
  have hrawC (p : Point3) (hp : p∈C) := hraw p (hCS hp)
  obtain ⟨hPts,hcard,hunit,hpointSep,hprofile⟩ := original_dense_graph_projected_owner_profile P Q C hC G b
    c rho Delta (M:ℝ) A lam K0 hDelta hMr hA hlam hlam1 hK0 h48
    (fun p hp => hbox p (hCP hp)) hrawC hsepC hUQ hmin hmax hGU hdense
    (fun p hp => hpotential p (hCS hp))
  have hinj := original_normalized_owner_injective b c rho Delta C hDelta h48 hrawC hsepC
  obtain ⟨hOwnerSub,hOwnerN,hOwnerMass,hOwnerRich⟩ := original_dense_rich_owner_graph P Q S C hC G
    Delta r (M:ℝ) A lam k hDelta hsmall hr hDr hMr hA hlam hk hSP hSU hUQ hG hbox hnear
    hsep hmin hmax hdense hrich
  have hHcard := original_normalized_owner_graph_card b G C hC hinj
  have hHmass : lam*((normalizedImage b C).card : ℝ)^2 ≤ A^2*(normalizedOwnerGraph b G C hC).card := by
    rw [hcard,hHcard]
    exact hOwnerMass
  have hHn : (normalizedOwnerGraph b G C hC).Nonempty := hOwnerN.image (pairCode (normalizedProject b))
  have hRich2 := original_normalized_owner_graph_richness b G C hC Delta r A k hA hinj hOwnerRich
  have hambient := original_dense_carrier_mass Q (originalCarrier P C hC (Delta/4)) G lam hlam.le hlam1 hGU hdense
  have hCap2 := original_normalized_owner_graph_cap P Q C hC G b c rho Delta r qcap (M:ℝ) A lam B
    hrho hDelta (by linarith only [hsmall,hDelta]) hDr hr h54 h48 hqcap hMr hB hlam.le
    hUQ hCQ hGU (fun p hp => hbox p (hQP hp)) hrawC hsepC hsep hmin hmax hambient hcap
  have hsum := (original_full_fiber_partition P S C hC (Delta/4) hSP hnear).2.2.1
  refine ⟨C,hC,M,hCS,hSU,hUQ,hM,hA1,(fun p hp => ⟨(hpop p hp).1,hmax p hp⟩),hsum,
    hPts,hcard,hunit,?_,?_,original_normalized_owner_graph_subset b G C hC,hHn,hHmass,?_⟩
  · intro p hp q hq hne
    simpa only [original_distance2_eq_a1_euclidean] using hpointSep p hp q hq hne
  · intro a R hR
    simpa only [original_distance2_eq_a1_euclidean] using hprofile a R hR
  · intro e he
    have hne : e.1≠e.2 := by
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨_z,_hz,_hzu,hgap,_hpop⟩ := hOwnerRich u hu
      obtain ⟨hu1,hu2⟩ := Finset.mem_product.mp (hOwnerSub hu)
      intro heq
      have heq' : u.1=u.2 := hinj hu1 hu2 heq
      rw [heq'] at hgap
      have hzero : distance3 u.2 u.2=0 := by simp only [distance3_eq_euclidean,dist_self]
      rw [hzero] at hgap
      linarith only [hgap,hr]
    obtain ⟨z,hz,heq,hpop⟩ := hRich2 e he
    exact ⟨hne,⟨z,hz,heq⟩,hpop,hCap2 e he⟩

end NativeOriginalUnweightedSliceFrame
