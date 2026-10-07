import Theorems.Thm_StickyKakeya4_native_two_stage_point_retention
import Theorems.Thm_StickyKakeya4_native_direction_rank_wedge
import Theorems.Thm_StickyKakeya4_native_incident_rank_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeTwoStageTransverseTuples
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeDirectionRankDichotomy NativeDirectionRankWedge NativeIncidentRankSelection
open NativeJointUniformCoarseRelations
open scoped BigOperators

lemma unit_mass_eq_card {α : Type*} [DecidableEq α] (A : Finset α) :
    mass (fun _ : α => (1:ℝ)) A = (A.card:ℝ) := by
  simp [mass]

lemma unit_chainMass_eq_card {α V : Type*} [DecidableEq α]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A : Finset α) (v : α → V) (q : ℝ) (ell : ℕ) :
    chainMass A v q (fun _ : α => (1:ℝ)) ell = ((chains A v q ell).card:ℝ) := by
  simp [chainMass,mass,chainWeight]

/-- Original concentration failure transfers to every retained point using
only the actual global retention and the two installed fine-point relations.
The pointwise retention inequality is proved, not supplied. -/
theorem point_near_le_half {n : ℕ} (D : FiniteScaleSource n)
    (E1 E2 : Finset (Fin n × Index)) (h21 : E2 ⊆ E1) (Q1 Q2 : ℕ)
    (H1 : HasUniformFibers E1 Q1 Prod.snd) (H2 : HasUniformFibers E2 Q2 Prod.snd)
    (lambda G Bscale : ℝ) (hlambda : 0 < lambda) (hG : 0 ≤ G) (hB : 0 ≤ Bscale)
    (hret : lambda*(E1.card:ℝ) ≤ G*E2.card)
    (hbudget : Bscale*G*(Q1:ℝ)^2*(Q2:ℝ)^2 ≤ lambda/2)
    (k : Index) (hk : k ∈ E2.image Prod.snd) (q : ℝ) (ell : ℕ)
    (Hfailed : ∀P : Submodule ℝ E4, Module.finrank ℝ P < ell →
      ((pointNear D E1 k q P).card:ℝ) ≤ Bscale*(pointSet E1 k).card) :
    ∀P : Submodule ℝ E4, Module.finrank ℝ P < ell →
      ((pointNear D E2 k q P).card:ℝ) ≤ ((pointSet E2 k).card:ℝ)/2 := by
  obtain ⟨z,hz,hzk⟩ := mem_image.mp hk
  have hpoint : lambda*((pointSet E1 k).card:ℝ) ≤
      G*(Q1:ℝ)^2*(Q2:ℝ)^2*((pointSet E2 k).card:ℝ) := by
    simpa only [pointSet,hzk] using
      NativeTwoStagePointRetention.point_retention_of_two_uniformities
        E1 E2 h21 Q1 Q2 H1 H2 lambda G hlambda.le hG hret z hz
  intro P hP
  have hsub : pointNear D E2 k q P ⊆ pointNear D E1 k q P :=
    filter_subset_filter _ (filter_subset_filter _ h21)
  have hc : ((pointNear D E2 k q P).card:ℝ) ≤ (pointNear D E1 k q P).card := by
    exact_mod_cast card_le_card hsub
  apply (mul_le_mul_iff_right₀ hlambda).mp
  calc
    _ ≤ lambda*((pointNear D E1 k q P).card:ℝ) :=
      mul_le_mul_of_nonneg_left hc hlambda.le
    _ ≤ lambda*(Bscale*((pointSet E1 k).card:ℝ)) :=
      mul_le_mul_of_nonneg_left (Hfailed P hP) hlambda.le
    _ = Bscale*(lambda*((pointSet E1 k).card:ℝ)) := by ring
    _ ≤ Bscale*(G*(Q1:ℝ)^2*(Q2:ℝ)^2*((pointSet E2 k).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hpoint hB
    _ = (Bscale*G*(Q1:ℝ)^2*(Q2:ℝ)^2)*((pointSet E2 k).card:ℝ) := by ring
    _ ≤ (lambda/2)*((pointSet E2 k).card:ℝ) :=
      mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The earlier-rank failure field, together with actual global retention,
constructs quantitatively transverse tuples at each surviving original point.
No refinement of E2 and no independence, wedge, or pointwise-retention premise
is used. Unit incidence weights make the tuple mass its literal cardinality. -/
theorem point_transverse_chains {n : ℕ} (D : FiniteScaleSource n)
    (E1 E2 : Finset (Fin n × Index)) (h21 : E2 ⊆ E1) (Q1 Q2 : ℕ)
    (H1 : HasUniformFibers E1 Q1 Prod.snd) (H2 : HasUniformFibers E2 Q2 Prod.snd)
    (lambda G Bscale : ℝ) (hlambda : 0 < lambda) (hG : 0 ≤ G) (hB : 0 ≤ Bscale)
    (hret : lambda*(E1.card:ℝ) ≤ G*E2.card)
    (hbudget : Bscale*G*(Q1:ℝ)^2*(Q2:ℝ)^2 ≤ lambda/2)
    (q : ℝ) (hq : 0 < q) (ell : ℕ)
    (Hfailed : ∀k∈E2.image Prod.snd, ∀P : Submodule ℝ E4,
      Module.finrank ℝ P < ell →
      ((pointNear D E1 k q P).card:ℝ) ≤ Bscale*(pointSet E1 k).card) :
    ∀k∈E2.image Prod.snd,
      let A := pointSet E2 k
      let v := fun z : Fin n × Index => slopeVector D z.1
      let C := chains A v q ell
      C.Nonempty ∧ ((A.card:ℝ)/2)^ell ≤ (C.card:ℝ) ∧
        ∀xs∈C, xs.length=ell ∧ (∀z∈xs,z∈E2 ∧ z.2=k) ∧
          Separated v q xs ∧ LinearIndependent ℝ (fun i : Fin xs.length => v (xs.get i)) ∧
          q^(2*ell) ≤ (Matrix.gram ℝ (fun i : Fin xs.length => v (xs.get i))).det := by
  intro k hk
  let A := pointSet E2 k
  let v := fun z : Fin n × Index => slopeVector D z.1
  let C := chains A v q ell
  have hhalf := point_near_le_half D E1 E2 h21 Q1 Q2 H1 H2 lambda G Bscale
    hlambda hG hB hret hbudget k hk q ell (Hfailed k hk)
  have hbound : ((A.card:ℝ)/2)^ell ≤ (C.card:ℝ) := by
    have hb : (A.card:ℝ)/2 ≤ mass (fun _ : Fin n × Index => (1:ℝ)) A := by
      rw [unit_mass_eq_card]
      have hc := Nat.cast_nonneg (α := ℝ) A.card
      linarith
    have hh := broad_chain_mass A v q (fun _ : Fin n × Index => (1:ℝ))
      (fun _ => by norm_num) ((A.card:ℝ)/2) hb (fun P hP => by
        rw [unit_mass_eq_card]
        exact hhalf P hP) ell le_rfl
    rw [unit_mass_eq_card,unit_chainMass_eq_card] at hh
    have he : (A.card:ℝ)-(A.card:ℝ)/2=(A.card:ℝ)/2 := by ring
    simpa only [he] using hh
  have hA : A.Nonempty := by
    obtain ⟨z,hz,hzk⟩ := mem_image.mp hk
    exact ⟨z,mem_filter.mpr ⟨hz,hzk⟩⟩
  have hC : C.Nonempty := by
    have ha : (0:ℝ) < A.card := by exact_mod_cast card_pos.mpr hA
    have hc : (0:ℝ) < C.card := (pow_pos (half_pos ha) ell).trans_le hbound
    exact card_pos.mp (by exact_mod_cast hc)
  refine ⟨hC,hbound,?_⟩
  intro xs hxs
  refine ⟨chains_length A v q ell xs hxs,?_,chains_separated A v q ell xs hxs,
    separated_linearIndependent v q hq xs (chains_separated A v q ell xs hxs),
    chains_gram_det_lower A v q hq ell xs hxs⟩
  intro z hz
  exact mem_filter.mp (chains_labels A v q ell xs hxs z hz)

/-- Adapter for exactly the finite earlier-rank/test-menu failure returned by
exists_rank_scale_retention. The immediately previous allowed rank controls
every subspace of dimension below the chosen actual rank. -/
theorem previous_rank_menu_transverse_chains {ι : Type*} [DecidableEq ι] {n : ℕ}
    (D : FiniteScaleSource n) (E1 F E2 : Finset (Fin n × Index))
    (hF1 : F ⊆ E1) (h2F : E2 ⊆ F) (Q1 Q2 : ℕ)
    (H1 : HasUniformFibers E1 Q1 Prod.snd) (H2 : HasUniformFibers E2 Q2 Prod.snd)
    (lambda G : ℝ) (hlambda : 0 < lambda) (hG : 0 ≤ G)
    (hret : lambda*(E1.card:ℝ) ≤ G*E2.card)
    (rank previous : Fin 4) (hprevious : previous.val+1=rank.val)
    (allowed : Fin 4 → Finset ι) (radius : ι → ℝ) (eta : Fin 4 → ℝ)
    (test : ι) (htest : test ∈ allowed previous) (hq : 0 < radius test)
    (Hfailed : ∀k∈F.image Prod.snd, ∀rank' : Fin 4, rank'<rank →
      ∀j∈allowed rank', ∀P : Submodule ℝ E4, Module.finrank ℝ P ≤ rank'.val+1 →
      ((pointNear D E1 k (radius j) P).card:ℝ) <
        (radius j)^(eta rank')*((pointSet E1 k).card:ℝ))
    (hbudget : (radius test)^(eta previous)*G*(Q1:ℝ)^2*(Q2:ℝ)^2 ≤ lambda/2) :
    ∀k∈E2.image Prod.snd,
      let A := pointSet E2 k
      let v := fun z : Fin n × Index => slopeVector D z.1
      let C := chains A v (radius test) (rank.val+1)
      C.Nonempty ∧ ((A.card:ℝ)/2)^(rank.val+1) ≤ (C.card:ℝ) ∧
        ∀xs∈C, xs.length=rank.val+1 ∧ (∀z∈xs,z∈E2 ∧ z.2=k) ∧
          Separated v (radius test) xs ∧
          LinearIndependent ℝ (fun i : Fin xs.length => v (xs.get i)) ∧
          (radius test)^(2*(rank.val+1)) ≤
            (Matrix.gram ℝ (fun i : Fin xs.length => v (xs.get i))).det := by
  apply point_transverse_chains D E1 E2 (h2F.trans hF1) Q1 Q2 H1 H2
    lambda G ((radius test)^(eta previous)) hlambda hG
    (Real.rpow_pos_of_pos hq _).le hret hbudget (radius test) hq (rank.val+1)
  intro k hk P hP
  have hkF : k∈F.image Prod.snd := image_subset_image h2F hk
  have hp : previous < rank := by
    change previous.val < rank.val
    omega
  exact (Hfailed k hkF previous hp test htest P (by omega)).le

end NativeTwoStageTransverseTuples
