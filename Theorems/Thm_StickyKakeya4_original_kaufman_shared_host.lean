import Theorems.Thm_StickyKakeya4_finite_kaufman_projection

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical

namespace OriginalKaufmanSharedHost
open ProjectionAnnulusEnergy

def stripConstant (n : ℕ) (KP KL eps : ℝ) : ℝ :=
  48*KP*KL*((n:ℝ)+3)^2/(eps^3*(1-eps))

/-- Removing a small set of original points has the same absolute mass cost
for every original subquery. -/
lemma original_intersection_loss {X : Type*} [DecidableEq X]
    (P V Q : Finset X) {eps : ℝ} (hVP : V ⊆ P) (hQP : Q ⊆ P)
    (hret : (1-eps)*(P.card:ℝ) ≤ V.card) :
    (Q.card:ℝ) ≤ (Q∩V).card+eps*P.card := by
  have hu : Q∪V ⊆ P := Finset.union_subset hQP hVP
  have huc : ((Q∪V).card:ℝ) ≤ P.card := Nat.cast_le.mpr (Finset.card_le_card hu)
  have hid : ((Q∪V).card:ℝ)+(Q∩V).card=Q.card+V.card := by
    exact_mod_cast Finset.card_union_add_card_inter Q V
  nlinarith only [huc,hid,hret]

/-- Original point and slope Frostman bounds produce a common host for any
two retained directions, with both actual strip profiles and a query-uniform
original mass budget. The queried carrier can be chosen after the directions. -/
theorem exists_original_shared_profile_host
    (P : Finset Point) (Lambda : Finset ℝ) (n : ℕ)
    {KP KL u eps : ℝ} (hPnon : P.Nonempty)
    (hKP : 1 ≤ KP) (hKL : 1 ≤ KL) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (heps : 0 < eps) (heps1 : eps < 1)
    (hP : ∀ p∈P, |p.1| ≤ 1 ∧ |p.2| ≤ 1)
    (hLambda : ∀ lam∈Lambda, |lam| ≤ 1)
    (hFP : PointFrostman P (mesh n) KP u)
    (hFL : SlopeFrostman Lambda (mesh n) KL u) :
    ∃ Lambda' : Finset ℝ, Lambda' ⊆ Lambda ∧
      (1-eps)*(Lambda.card:ℝ) ≤ Lambda'.card ∧
      ∀ a∈Lambda', ∀ b∈Lambda', ∀ C : Finset Point, C ⊆ P →
        ∃ S : Finset Point, S ⊆ C ∧
          (∀ Q : Finset Point, Q ⊆ C →
            (Q.card:ℝ) ≤ (Q∩S).card+2*eps*P.card) ∧
          ∀ lam : ℝ, lam=a ∨ lam=b →
            ∀ c r : ℝ, mesh n ≤ r → r ≤ 1 →
              ((S.filter (fun p => |projection lam p-c| ≤ r)).card:ℝ) ≤
                stripConstant n KP KL eps*r^u*P.card := by
  obtain ⟨L,hLC,hLmass,hgood⟩ :=
    FiniteKaufmanProjection.finite_kaufman_projection P Lambda n KP KL u eps
      hPnon hKP hKL hu hu1 heps heps1 hP hLambda hFP hFL
  refine ⟨L,hLC,hLmass,?_⟩
  intro a ha b hb C hCP
  obtain ⟨V,hVP,hVmass,hVprofile⟩ := hgood a ha
  obtain ⟨W,hWP,hWmass,hWprofile⟩ := hgood b hb
  let S := (C∩V)∩W
  have hSC : S ⊆ C := Finset.inter_subset_left.trans Finset.inter_subset_left
  have hSV : S ⊆ V := Finset.inter_subset_left.trans Finset.inter_subset_right
  have hSW : S ⊆ W := Finset.inter_subset_right
  have hH : 0 ≤ stripConstant n KP KL eps := by
    unfold stripConstant
    have hc : 0 < 1-eps := sub_pos.mpr heps1
    positivity
  have hmassV : eps*(V.card:ℝ) ≤ V.card := by
    have hc := mul_le_mul_of_nonneg_right heps1.le (show (0:ℝ) ≤ V.card from Nat.cast_nonneg _)
    simpa only [one_mul] using hc
  have hmassW : eps*(W.card:ℝ) ≤ W.card := by
    have hc := mul_le_mul_of_nonneg_right heps1.le (show (0:ℝ) ≤ W.card from Nat.cast_nonneg _)
    simpa only [one_mul] using hc
  refine ⟨S,hSC,?_,?_⟩
  · intro Q hQC
    have hQ := original_intersection_loss P V Q hVP (hQC.trans hCP) hVmass
    have hQ' := original_intersection_loss P W (Q∩V) hWP
      (Finset.inter_subset_left.trans (hQC.trans hCP)) hWmass
    have hid : (Q∩V)∩W=Q∩S := by
      ext p
      simp only [S,Finset.mem_inter]
      constructor
      · rintro ⟨⟨hpQ,hpV⟩,hpW⟩
        exact ⟨hpQ,⟨hQC hpQ,hpV⟩,hpW⟩
      · rintro ⟨hpQ,⟨_hpC,hpV⟩,hpW⟩
        exact ⟨⟨hpQ,hpV⟩,hpW⟩
    rw [hid] at hQ'
    nlinarith only [hQ,hQ']
  · intro lam hlam c r hr hr1
    have hrpos := (mesh_pos n).trans_le hr
    have hcoef : 0 ≤ stripConstant n KP KL eps*r^u := by positivity
    rcases hlam with rfl|rfl
    · have hv := hVprofile V Finset.Subset.rfl hmassV c r hr hr1
      have hc : ((S.filter (fun p => |projection lam p-c| ≤ r)).card:ℝ) ≤
          (V.filter (fun p => |projection lam p-c| ≤ r)).card :=
        Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter
          (fun p => |projection lam p-c| ≤ r) hSV))
      have hp := mul_le_mul_of_nonneg_left
        (show (V.card:ℝ) ≤ P.card from Nat.cast_le.mpr (Finset.card_le_card hVP)) hcoef
      exact hc.trans (hv.trans hp)
    · have hw := hWprofile W Finset.Subset.rfl hmassW c r hr hr1
      have hc : ((S.filter (fun p => |projection lam p-c| ≤ r)).card:ℝ) ≤
          (W.filter (fun p => |projection lam p-c| ≤ r)).card :=
        Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter
          (fun p => |projection lam p-c| ≤ r) hSW))
      have hp := mul_le_mul_of_nonneg_left
        (show (W.card:ℝ) ≤ P.card from Nat.cast_le.mpr (Finset.card_le_card hWP)) hcoef
      exact hc.trans (hw.trans hp)

end OriginalKaufmanSharedHost
