import Theorems.Thm_StickyKakeya4_original_transverse_query_selection
import Theorems.Thm_StickyKakeya4_original_two_projection_cover
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
open Classical

namespace OriginalNativeTransverseQueries
open OriginalTransverseQuerySelection ProjectionAnnulusEnergy
open OriginalTwoProjectionCartesian OriginalTwoProjectionCover

def awayTwo (D : Finset ℝ) (a b h : ℝ) : Finset ℝ :=
  D.filter (fun c => h ≤ |c-a| ∧ h ≤ |c-b|)

/-- Delete two literal original slope intervals, paying their original counts. -/
lemma away_two_card (C D : Finset ℝ) (a b h cap : ℝ) (hD : D ⊆ C)
    (ha : ((C.filter (fun c => |c-a|≤h)).card : ℝ) ≤ cap)
    (hb : ((C.filter (fun c => |c-b|≤h)).card : ℝ) ≤ cap) :
    (D.card : ℝ)-2*cap ≤ (awayTwo D a b h).card := by
  have hcover : D ⊆ (awayTwo D a b h ∪ C.filter (fun c => |c-a|≤h)) ∪
      C.filter (fun c => |c-b|≤h) := by
    intro c hc
    by_cases hca : h ≤ |c-a|
    · by_cases hcb : h ≤ |c-b|
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hc,hca,hcb⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hD hc,(lt_of_not_ge hcb).le⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hD hc,(lt_of_not_ge hca).le⟩))
  have hnat := (Finset.card_le_card hcover).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hreal : (D.card : ℝ) ≤ (awayTwo D a b h).card+
      (C.filter (fun c => |c-a|≤h)).card+(C.filter (fun c => |c-b|≤h)).card := by
    exact_mod_cast hnat
  linarith

/-- Original slope Frostman counts construct two transverse source slopes and
many third slopes away from both; all queries remain original intersections. -/
theorem exists_native_transverse_common_queries
    {X : Type*} [DecidableEq X] (P : Finset X) (C : Finset ℝ) (Q : ℝ → Finset X)
    {q h delta K s : ℝ} (hP : P.Nonempty) (hC : C.Nonempty) (hq : 0 < q)
    (hscale : delta ≤ h) (hh1 : h ≤ 1)
    (hprofile : SlopeFrostman C delta K s) (hbudget : K*h^s ≤ q^3/16)
    (hQ : ∀ c ∈ C, Q c ⊆ P) (hmass : ∀ c ∈ C, q*(P.card : ℝ) ≤ (Q c).card) :
    ∃ a ∈ C, ∃ b ∈ C, h ≤ |a-b| ∧
      ∃ C' : Finset ℝ, C' ⊆ C ∧ (q^3/8)*(C.card : ℝ) ≤ C'.card ∧
        (Q a ∩ Q b) ⊆ P ∧ (q^3/4)*(P.card : ℝ) ≤ (Q a ∩ Q b).card ∧
        ∀ c ∈ C', h ≤ |c-a| ∧ h ≤ |c-b| ∧
          (q^3/4)*(P.card : ℝ) ≤ ((Q a ∩ Q b) ∩ Q c).card := by
  have hinterval (a : ℝ) : ((C.filter (fun c => |c-a|≤h)).card : ℝ) ≤ (q^3/16)*C.card :=
    (hprofile a h hscale hh1).trans
      (mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg _))
  have hclose : ∀ a ∈ C, ((C.filter (fun b => |a-b|<h)).card : ℝ) ≤ (q^3/2)*C.card := by
    intro a _ha
    have hsub : C.filter (fun b => |a-b|<h) ⊆ C.filter (fun b => |b-a|≤h) := by
      intro b hb
      obtain ⟨hbC,hab⟩ := Finset.mem_filter.mp hb
      exact Finset.mem_filter.mpr ⟨hbC,by simpa only [abs_sub_comm] using hab.le⟩
    have hh := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hinterval a)
    have hnon : 0 ≤ q^3*(C.card : ℝ) := by positivity
    nlinarith
  obtain ⟨a,ha,b,hb,hab,D,hDC,hDmass,hcarrier,hcarrierMass,hqueries⟩ :=
    exists_original_transverse_common_queries P C Q hP hC hq hQ hmass hclose
  let C' := awayTwo D a b h
  have hCD : C' ⊆ D := Finset.filter_subset _ _
  have hmass' := away_two_card C D a b h ((q^3/16)*C.card) hDC (hinterval a) (hinterval b)
  have hC'mass : (q^3/8)*(C.card : ℝ) ≤ C'.card := by
    dsimp [C']
    nlinarith only [hmass',hDmass]
  refine ⟨a,ha,b,hb,hab,C',hCD.trans hDC,hC'mass,hcarrier,hcarrierMass,?_⟩
  intro c hc
  exact ⟨(Finset.mem_filter.mp hc).2.1,(Finset.mem_filter.mp hc).2.2,hqueries c (hCD hc)⟩

/-- Keeping the third original slope away from both chosen slopes supplies
the lower coefficient bounds needed before applying separated real BSG. -/
theorem weights_lower_of_three_transverse {h a b c : ℝ} (hh : 0 < h)
    (hab : h ≤ |a-b|) (hca : h ≤ |c-a|) (hcb : h ≤ |c-b|)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    h/2 ≤ |leftWeight a b c| ∧ h/2 ≤ |rightWeight a b c| := by
  have hden : 0 < |b-a| := by simpa only [abs_sub_comm] using hh.trans_le hab
  have hden2 : |b-a| ≤ 2 := by
    have ht := abs_add_le b (-a)
    simp only [← sub_eq_add_neg,abs_neg] at ht
    linarith
  constructor
  · dsimp [leftWeight]
    rw [abs_div]
    apply (le_div_iff₀ hden).mpr
    have hn : h ≤ |b-c| := by simpa only [abs_sub_comm] using hcb
    nlinarith only [hn,mul_le_mul_of_nonneg_left hden2 hh.le]
  · dsimp [rightWeight]
    rw [abs_div]
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hca,mul_le_mul_of_nonneg_left hden2 hh.le]

end OriginalNativeTransverseQueries
