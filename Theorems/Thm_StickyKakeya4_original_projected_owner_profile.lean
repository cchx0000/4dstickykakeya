import Theorems.Thm_StickyKakeya4_original_three_dimensional_raw_owner_net
import Theorems.Thm_StickyKakeya4_original_balanced_owner_counts
import Theorems.Thm_StickyKakeya4_original_three_dimensional_slice_energy_basic
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
noncomputable section
namespace OriginalProjectedOwnerProfile
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalLiteralSlabCover OriginalThreeDimensionalSlabProjection
open OriginalThreeDimensionalVoronoiFibers OriginalThreeDimensionalFiberSlabGeometry
open OriginalThreeDimensionalAveragedSliceEnergy OriginalFiniteCellWeights
open OriginalBalancedOwnerCounts

def normalizedProject (b : Frame3) (x : Point3) : Point2 :=
  ((project b x).1/4,(project b x).2/4)

def normalizedImage (b : Frame3) (C : Finset Point3) : Finset Point2 :=
  C.image (normalizedProject b)

def centerRegion (b : Frame3) (C : Finset Point3) (a : Point2) (R : ℝ) : Finset Point3 :=
  C.filter (fun c => distance2 a (normalizedProject b c) ≤ R)

lemma original_normalized_project_distance (b : Frame3) (p q : Point3) :
    distance2 (normalizedProject b p) (normalizedProject b q)=
      distance2 (project b p) (project b q)/4 := by
  have hs : distance2 (normalizedProject b p) (normalizedProject b q)^2=
      distance2 (project b p) (project b q)^2/16 := by
    rw [distance2_squared,distance2_squared]
    dsimp only [normalizedProject]
    ring
  have h1 : 0 ≤ distance2 (normalizedProject b p) (normalizedProject b q) := dist_nonneg
  have h2 : 0 ≤ distance2 (project b p) (project b q) := dist_nonneg
  nlinarith only [hs,h1,h2]

lemma original_normalized_project_box (b : Frame3) (p : Point3)
    (hp : ∀ j,|p j| ≤ 1) :
    |(normalizedProject b p).1| ≤ 1 ∧ |(normalizedProject b p).2| ≤ 1 := by
  obtain ⟨h1,h2⟩ := original_projected_coordinate_bounds b p hp
  simp only [normalizedProject,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 4)]
  constructor <;> linarith

lemma original_normalized_owner_separation (b : Frame3) (c rho Delta : ℝ)
    (C : Finset Point3) (hsmall : 48*rho ≤ Delta)
    (hraw : ∀ p∈C,|frameCoordinate b 2 p-c| ≤ 3*rho)
    (hsep : ∀ p∈C,∀ q∈C,p≠q → Delta/4 ≤ distance3 p q) :
    ∀ p∈C,∀ q∈C,p≠q →
      Delta/32 ≤ distance2 (normalizedProject b p) (normalizedProject b q) := by
  intro p hp q hq hne
  rw [original_normalized_project_distance]
  have hh := original_raw_net_projected_separation b c rho Delta p q
    (hraw p hp) (hraw q hq) (hsep p hp q hq hne) hsmall
  linarith only [hh]

lemma original_normalized_owner_injective (b : Frame3) (c rho Delta : ℝ)
    (C : Finset Point3) (hDelta : 0 < Delta) (hsmall : 48*rho ≤ Delta)
    (hraw : ∀ p∈C,|frameCoordinate b 2 p-c| ≤ 3*rho)
    (hsep : ∀ p∈C,∀ q∈C,p≠q → Delta/4 ≤ distance3 p q) :
    Set.InjOn (normalizedProject b) C := by
  intro p hp q hq he
  by_contra hne
  have hh := original_normalized_owner_separation b c rho Delta C hsmall hraw hsep p hp q hq hne
  rw [he] at hh
  have hz : distance2 (normalizedProject b q) (normalizedProject b q)=0 := dist_self _
  rw [hz] at hh
  linarith only [hh,hDelta]

lemma original_normalized_owner_card (b : Frame3) (c rho Delta : ℝ)
    (C : Finset Point3) (hDelta : 0 < Delta) (hsmall : 48*rho ≤ Delta)
    (hraw : ∀ p∈C,|frameCoordinate b 2 p-c| ≤ 3*rho)
    (hsep : ∀ p∈C,∀ q∈C,p≠q → Delta/4 ≤ distance3 p q) :
    (normalizedImage b C).card=C.card :=
  Finset.card_image_of_injOn (original_normalized_owner_injective b c rho Delta C hDelta hsmall hraw hsep)

/-- An arbitrary planar query is pulled back to the exact retained centers,
without changing or merging their original labels. -/
lemma original_normalized_region_readback (b : Frame3) (C : Finset Point3)
    (a : Point2) (R : ℝ) :
    (normalizedImage b C).filter (fun z => distance2 a z ≤ R)=
      (centerRegion b C a R).image (normalizedProject b) := by
  ext z
  constructor
  · intro hz
    obtain ⟨hzI,hzr⟩ := Finset.mem_filter.mp hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hzI
    exact Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,hzr⟩,rfl⟩
  · intro hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hpC,hpr⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hpC,hpr⟩

/-- The FULL original fibers over a planar query ball lie in a single
original ball about a retained center. Raw-slab normal errors and the actual
owner radius are paid before any population estimate is applied. -/
theorem original_owner_region_in_original_ball (P Q C : Finset Point3)
    (hC : C.Nonempty) (b : Frame3) (c rho Delta : ℝ)
    (hsmall : 48*rho ≤ Delta)
    (hraw : ∀ p∈C,|frameCoordinate b 2 p-c| ≤ 3*rho)
    (hUQ : originalCarrier P C hC (Delta/4)⊆Q)
    (a : Point2) (R : ℝ) (hR : Delta/32 ≤ R)
    (p : Point3) (hp : p∈centerRegion b C a R) :
    (originalCarrier P C hC (Delta/4)).filter
      (fun x => originalOwner C hC x∈centerRegion b C a R)⊆
      Q.filter (fun x => distance3 p x ≤ 32*R) := by
  obtain ⟨hpC,hpr⟩ := Finset.mem_filter.mp hp
  intro x hx
  obtain ⟨hxU,hxo⟩ := Finset.mem_filter.mp hx
  obtain ⟨hoC,hor⟩ := Finset.mem_filter.mp hxo
  have hn := (Finset.mem_filter.mp hxU).2
  have ht : distance2 (normalizedProject b p) (normalizedProject b (originalOwner C hC x)) ≤
      distance2 a (normalizedProject b p)+distance2 a (normalizedProject b (originalOwner C hC x)) := by
    unfold distance2
    exact dist_triangle_left _ _ _
  rw [original_normalized_project_distance] at ht
  have hd := original_slab_distance_comparison b c (3*rho) p (originalOwner C hC x)
    (hraw p hpC) (hraw _ hoC)
  have htri : distance3 p x ≤ distance3 p (originalOwner C hC x)+distance3 x (originalOwner C hC x) := by
    simp only [distance3_eq_euclidean]
    exact dist_triangle_right _ _ _
  have hRp : 0 ≤ R := (show 0 ≤ distance2 a (normalizedProject b p) from dist_nonneg).trans hpr
  exact Finset.mem_filter.mpr ⟨hUQ hxU,by linarith only [ht,hpr,hor,hd,htri,hn,hsmall,hR,hRp]⟩

/-- The original Q-potential controls the complete preimage of a planar
ball. The potential is evaluated at one actual retained original center. -/
theorem original_owner_region_original_mass (P Q C : Finset Point3)
    (hC : C.Nonempty) (b : Frame3) (c rho Delta K0 : ℝ)
    (hDelta : 0 < Delta) (hK0 : 0 ≤ K0) (hsmall : 48*rho ≤ Delta)
    (hraw : ∀ p∈C,|frameCoordinate b 2 p-c| ≤ 3*rho)
    (hUQ : originalCarrier P C hC (Delta/4)⊆Q)
    (hpotential : ∀ p∈C,slicePotential Q Delta p ≤ K0*Q.card)
    (a : Point2) (R : ℝ) (hR : Delta/32 ≤ R) :
    (((originalCarrier P C hC (Delta/4)).filter
      (fun x => originalOwner C hC x∈centerRegion b C a R)).card : ℝ) ≤
      (32*K0*R)*Q.card := by
  by_cases hD : (centerRegion b C a R).Nonempty
  · obtain ⟨p,hp⟩ := hD
    have hsub := original_owner_region_in_original_ball P Q C hC b c rho Delta hsmall hraw hUQ a R hR p hp
    have hcount := original_ball_count_from_slice_potential Q Delta (32*R) p hDelta
      (by linarith only [hR])
    have hcap := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hcount
    have hpot := mul_le_mul_of_nonneg_left (hpotential p (Finset.mem_filter.mp hp).1)
      (show 0 ≤ 32*R by linarith only [hDelta,hR])
    nlinarith only [hcap,hpot]
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hD
    rw [hempty]
    have hRp : 0 ≤ R := by linarith only [hDelta,hR]
    simpa using (show (0:ℝ) ≤ (32*K0*R)*Q.card by positivity)

/-- Balanced FULL original fibers transfer the Q-potential to the actual
unweighted normalized image, with the exact ambient retention loss. -/
theorem original_normalized_owner_profile (P Q C : Finset Point3)
    (hC : C.Nonempty) (b : Frame3) (c rho Delta M A lam K0 : ℝ)
    (hDelta : 0 < Delta) (hM : 0 < M) (_hA : 0 ≤ A) (hlam : 0 < lam)
    (hK0 : 0 ≤ K0) (hsmall : 48*rho ≤ Delta)
    (hraw : ∀ p∈C,|frameCoordinate b 2 p-c| ≤ 3*rho)
    (hsep : ∀ p∈C,∀ q∈C,p≠q → Delta/4 ≤ distance3 p q)
    (hUQ : originalCarrier P C hC (Delta/4)⊆Q)
    (hmin : ∀ p∈C,M ≤ ((originalFiber P C hC (Delta/4) p).card : ℝ))
    (hmax : ∀ p∈C,((originalFiber P C hC (Delta/4) p).card : ℝ) ≤ A*M)
    (hambient : lam*Q.card ≤ ((originalCarrier P C hC (Delta/4)).card : ℝ))
    (hpotential : ∀ p∈C,slicePotential Q Delta p ≤ K0*Q.card) :
    ∀ a : Point2,∀ R : ℝ,Delta/32 ≤ R →
      (((normalizedImage b C).filter (fun z => distance2 a z ≤ R)).card : ℝ) ≤
        (32*A*K0/lam)*R*(normalizedImage b C).card := by
  intro a R hR
  have hcap := original_owner_region_original_mass P Q C hC b c rho Delta K0
    hDelta hK0 hsmall hraw hUQ hpotential a R hR
  have hRp : 0 ≤ R := by linarith only [hDelta,hR]
  have hcount := original_owner_region_count Q (originalCarrier P C hC (Delta/4))
    C (centerRegion b C a R) (originalOwner C hC) M A lam (32*K0*R) hM
    (by positivity) hlam.le
    (Finset.filter_subset _ _) (fun x _hx => original_owner_mem C hC x)
    hmin hmax hambient hcap
  have himage : (((normalizedImage b C).filter (fun z => distance2 a z ≤ R)).card : ℝ) ≤
      ((centerRegion b C a R).card : ℝ) := by
    rw [original_normalized_region_readback]
    exact Nat.cast_le.mpr Finset.card_image_le
  have hmul := mul_le_mul_of_nonneg_left himage hlam.le
  rw [original_normalized_owner_card b c rho Delta C hDelta hsmall hraw hsep]
  apply (mul_le_mul_iff_of_pos_left hlam).mp
  have he : lam*((32*A*K0/lam)*R*C.card)=A*(32*K0*R)*C.card := by
    field_simp [ne_of_gt hlam]
  rw [he]
  exact hmul.trans hcount

/-- The SAME original owner net gives the unit-box, Euclidean-separated
planar point set. Its point profile is derived from full fibers and original
potentials, with exact source cardinality. -/
theorem original_projected_owner_point_profile (P Q C : Finset Point3)
    (hC : C.Nonempty) (b : Frame3) (c rho Delta M A lam K0 : ℝ)
    (hDelta : 0 < Delta) (hM : 0 < M) (hA : 0 ≤ A) (hlam : 0 < lam)
    (hK0 : 0 ≤ K0) (hsmall : 48*rho ≤ Delta)
    (hbox : ∀ p∈C,∀ j,|p j| ≤ 1)
    (hraw : ∀ p∈C,|frameCoordinate b 2 p-c| ≤ 3*rho)
    (hsep : ∀ p∈C,∀ q∈C,p≠q → Delta/4 ≤ distance3 p q)
    (hUQ : originalCarrier P C hC (Delta/4)⊆Q)
    (hmin : ∀ p∈C,M ≤ ((originalFiber P C hC (Delta/4) p).card : ℝ))
    (hmax : ∀ p∈C,((originalFiber P C hC (Delta/4) p).card : ℝ) ≤ A*M)
    (hambient : lam*Q.card ≤ ((originalCarrier P C hC (Delta/4)).card : ℝ))
    (hpotential : ∀ p∈C,slicePotential Q Delta p ≤ K0*Q.card) :
    (normalizedImage b C).Nonempty ∧ (normalizedImage b C).card=C.card ∧
      (∀ z∈normalizedImage b C,|z.1| ≤ 1 ∧ |z.2| ≤ 1) ∧
      (∀ z∈normalizedImage b C,∀ w∈normalizedImage b C,z≠w → Delta/32 ≤ distance2 z w) ∧
      ∀ a : Point2,∀ R : ℝ,Delta/32 ≤ R →
        (((normalizedImage b C).filter (fun z => distance2 a z ≤ R)).card : ℝ) ≤
          (32*A*K0/lam)*R*(normalizedImage b C).card := by
  refine ⟨hC.image _,original_normalized_owner_card b c rho Delta C hDelta hsmall hraw hsep,?_,?_,
    original_normalized_owner_profile P Q C hC b c rho Delta M A lam K0
      hDelta hM hA hlam hK0 hsmall hraw hsep hUQ hmin hmax hambient hpotential⟩
  · intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    exact original_normalized_project_box b p (hbox p hp)
  · intro z hz w hw hne
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hw
    exact original_normalized_owner_separation b c rho Delta C hsmall hraw hsep p hp q hq
      (fun he => hne (congrArg (normalizedProject b) he))

/-- Dense actual original pairs supply the ambient retention input; no
projected point-profile or restricted-fiber regularity is postulated. -/
theorem original_dense_graph_projected_owner_profile (P Q C : Finset Point3)
    (hC : C.Nonempty) (G : Finset (Point3 × Point3)) (b : Frame3) (c rho Delta M A lam K0 : ℝ)
    (hDelta : 0 < Delta) (hM : 0 < M) (hA : 0 ≤ A) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hK0 : 0 ≤ K0) (hsmall : 48*rho ≤ Delta)
    (hbox : ∀ p∈C,∀ j,|p j| ≤ 1)
    (hraw : ∀ p∈C,|frameCoordinate b 2 p-c| ≤ 3*rho)
    (hsep : ∀ p∈C,∀ q∈C,p≠q → Delta/4 ≤ distance3 p q)
    (hUQ : originalCarrier P C hC (Delta/4)⊆Q)
    (hmin : ∀ p∈C,M ≤ ((originalFiber P C hC (Delta/4) p).card : ℝ))
    (hmax : ∀ p∈C,((originalFiber P C hC (Delta/4) p).card : ℝ) ≤ A*M)
    (hG : G⊆(originalCarrier P C hC (Delta/4)).product (originalCarrier P C hC (Delta/4)))
    (hdense : lam*(Q.card : ℝ)^2 ≤ G.card)
    (hpotential : ∀ p∈C,slicePotential Q Delta p ≤ K0*Q.card) :
    (normalizedImage b C).Nonempty ∧ (normalizedImage b C).card=C.card ∧
      (∀ z∈normalizedImage b C,|z.1| ≤ 1 ∧ |z.2| ≤ 1) ∧
      (∀ z∈normalizedImage b C,∀ w∈normalizedImage b C,z≠w → Delta/32 ≤ distance2 z w) ∧
      ∀ a : Point2,∀ R : ℝ,Delta/32 ≤ R →
        (((normalizedImage b C).filter (fun z => distance2 a z ≤ R)).card : ℝ) ≤
          (32*A*K0/lam)*R*(normalizedImage b C).card := by
  exact original_projected_owner_point_profile P Q C hC b c rho Delta M A lam K0
    hDelta hM hA hlam hK0 hsmall hbox hraw hsep hUQ hmin hmax
    (original_dense_carrier_mass Q (originalCarrier P C hC (Delta/4)) G lam hlam.le hlam1 hG hdense)
    hpotential

end OriginalProjectedOwnerProfile
