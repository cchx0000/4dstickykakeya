import Theorems.Thm_StickyKakeya4_native_two_stage_transverse_tuples

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

noncomputable section
namespace NativeTwoStagePlaneRank
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeDirectionRankDichotomy NativeIncidentRankSelection
open NativeJointUniformCoarseRelations NativeTwoStageTransverseTuples

/-- If every surviving original label lies near P at radius r≤q, a proved
half-mass bound at q rules out dim(P)<ell. The upper rank bound then becomes
an exact rank, using only positivity of the literal original point fiber. -/
theorem point_plane_rank_eq {n : ℕ} (D : FiniteScaleSource n)
    (E : Finset (Fin n × Index)) (k : Index) (hk : k∈E.image Prod.snd)
    (P : Submodule ℝ E4) (ell : ℕ) (hdim : Module.finrank ℝ P ≤ ell)
    (r q : ℝ) (hrq : r ≤ q)
    (hnear : ∀z∈pointSet E k, Metric.infDist (slopeVector D z.1) (P:Set E4) ≤ r)
    (hhalf : ∀Q : Submodule ℝ E4, Module.finrank ℝ Q < ell →
      ((pointNear D E k q Q).card:ℝ) ≤ ((pointSet E k).card:ℝ)/2) :
    Module.finrank ℝ P = ell := by
  have he : pointNear D E k q P = pointSet E k := by
    apply filter_eq_self.mpr
    intro z hz
    exact (hnear z hz).trans hrq
  have hA : (pointSet E k).Nonempty := by
    obtain ⟨z,hz,hzk⟩ := mem_image.mp hk
    exact ⟨z,mem_filter.mpr ⟨hz,hzk⟩⟩
  have hc : (0:ℝ) < (pointSet E k).card := by exact_mod_cast card_pos.mpr hA
  by_contra hne
  have hlt : Module.finrank ℝ P < ell := by omega
  have hh := hhalf P hlt
  rw [he] at hh
  linarith

/-- Exact dimension of the SAME selected plane at every surviving original
point. All quantitative retention is derived from original global retention
and installed fine-point uniformities. The only test-radius facts are its
actual previous-rank menu membership and its ordering above the stopping radius.
No exact-rank or pointwise-retention certificate is assumed. -/
theorem previous_rank_menu_plane_rank {ι : Type*} [DecidableEq ι] {n : ℕ}
    (D : FiniteScaleSource n) (E1 F E2 : Finset (Fin n × Index))
    (hF1 : F ⊆ E1) (h2F : E2 ⊆ F) (Q1 Q2 : ℕ)
    (H1 : HasUniformFibers E1 Q1 Prod.snd) (H2 : HasUniformFibers E2 Q2 Prod.snd)
    (lambda G : ℝ) (hlambda : 0 < lambda) (hG : 0 ≤ G)
    (hret : lambda*(E1.card:ℝ) ≤ G*E2.card)
    (rank previous : Fin 4) (hprevious : previous.val+1=rank.val)
    (P : Index → Submodule ℝ E4) (r : ℝ)
    (hdim : ∀k∈F.image Prod.snd, Module.finrank ℝ (P k) ≤ rank.val+1)
    (hnear : ∀z∈F, Metric.infDist (slopeVector D z.1) (P z.2:Set E4) ≤ r)
    (allowed : Fin 4 → Finset ι) (radius : ι → ℝ) (eta : Fin 4 → ℝ)
    (test : ι) (htest : test∈allowed previous) (hq : 0 < radius test)
    (hrq : r ≤ radius test)
    (Hfailed : ∀k∈F.image Prod.snd, ∀rank' : Fin 4, rank'<rank →
      ∀j∈allowed rank', ∀Q : Submodule ℝ E4, Module.finrank ℝ Q ≤ rank'.val+1 →
      ((pointNear D E1 k (radius j) Q).card:ℝ) <
        (radius j)^(eta rank')*((pointSet E1 k).card:ℝ))
    (hbudget : (radius test)^(eta previous)*G*(Q1:ℝ)^2*(Q2:ℝ)^2 ≤ lambda/2) :
    ∀k∈E2.image Prod.snd, Module.finrank ℝ (P k) = rank.val+1 := by
  intro k hk
  have hkF : k∈F.image Prod.snd := image_subset_image h2F hk
  have hprev : previous < rank := by
    change previous.val < rank.val
    omega
  have hhalf := point_near_le_half D E1 E2 (h2F.trans hF1) Q1 Q2 H1 H2
    lambda G ((radius test)^(eta previous)) hlambda hG
    (Real.rpow_pos_of_pos hq _).le hret hbudget k hk (radius test) (rank.val+1)
    (fun Q hQ => (Hfailed k hkF previous hprev test htest Q (by omega)).le)
  apply point_plane_rank_eq D E2 k hk (P k) (rank.val+1) (hdim k hkF)
    r (radius test) hrq _ hhalf
  intro z hz
  obtain ⟨hzE,hzk⟩ := mem_filter.mp hz
  have hh := hnear z (h2F hzE)
  simpa only [hzk] using hh

end NativeTwoStagePlaneRank
