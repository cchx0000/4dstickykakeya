import Theorems.Thm_StickyKakeya4_original_native_transverse_queries
import Theorems.Thm_StickyKakeya4_original_profiled_third_query_family
import Theorems.Thm_StickyKakeya4_gkz_original_gap_energy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
open Classical

namespace OriginalFreshProjectionQueries
open OriginalNativeTransverseQueries OriginalProfiledThirdQueryFamily ProjectionAnnulusEnergy
open GKZOriginalGapEnergy
variable {X : Type*}

def bad (C : Finset ℝ) (F : Finset X) (q M : ℝ) (cover : ℝ → Finset X → ℝ) : Finset ℝ :=
  C.filter (fun c => ∃ Q : Finset X, Q⊆F ∧ q*(F.card:ℝ) ≤ Q.card ∧ cover c Q ≤ M)

/-- Literal failure of the local robust conclusion on EVERY admissible
original source subset. It can be re-used only after that subset's size is proved. -/
def Failure (P : Finset X) (C : Finset ℝ) (mass q beta M : ℝ)
    (cover : ℝ → Finset X → ℝ) : Prop :=
  ∀ F : Finset X, F⊆P → mass*(P.card:ℝ) ≤ F.card →
    beta*(C.card:ℝ) ≤ (bad C F q M cover).card

lemma original_bad_subset (C : Finset ℝ) (F : Finset X) (q M : ℝ) (cover : ℝ → Finset X → ℝ) :
    bad C F q M cover⊆C := Finset.filter_subset _ _

/-- Actual fresh witnesses for the newly selected source. No earlier query
family is asserted to survive an arbitrary BSG restriction. -/
theorem exists_original_bad_query_family (C : Finset ℝ) (F : Finset X) (q M : ℝ)
    (cover : ℝ → Finset X → ℝ) :
    ∃ Q : ℝ → Finset X, ∀ c∈bad C F q M cover,
      Q c⊆F ∧ q*(F.card:ℝ) ≤ (Q c).card ∧ cover c (Q c) ≤ M := by
  let D := bad C F q M cover
  have hw (c : ℝ) (hc : c∈D) : ∃ Q : Finset X,
      Q⊆F ∧ q*(F.card:ℝ) ≤ Q.card ∧ cover c Q ≤ M := (Finset.mem_filter.mp hc).2
  let Q : ℝ → Finset X := fun c => if hc : c∈D then Classical.choose (hw c hc) else ∅
  refine ⟨Q,?_⟩
  intro c hc
  dsimp [Q]
  rw [dif_pos hc]
  exact Classical.choose_spec (hw c hc)

/-- After a genuine original core F has been proved admissible, universal
failure gives fresh transverse original coefficients and fresh dense queries
inside THAT F, together with their inherited full original coefficient profile. -/
theorem exists_fresh_original_transverse_queries
    (P F : Finset X) (C : Finset ℝ) (cover : ℝ → Finset X → ℝ)
    {mass q beta M delta K u h a b : ℝ}
    (hC : C.Nonempty) (hd : 0 ≤ delta) (hK : 0 ≤ K) (hbeta : 0 < beta)
    (hscale : delta ≤ h) (hh1 : h ≤ 1) (hbudget : K*h^u ≤ beta/4)
    (hprofile : ScalarFrostman C delta K u)
    (hfailure : Failure P C mass q beta M cover)
    (hFP : F⊆P) (hFmass : mass*(P.card:ℝ) ≤ F.card) :
    ∃ D : Finset ℝ, D⊆C ∧ D.Nonempty ∧ (beta/2)*(C.card:ℝ) ≤ D.card ∧
      ScalarFrostman D delta (2*K/beta) u ∧
      ∃ Q : ℝ → Finset X, ∀ c∈D,
        h ≤ |c-a| ∧ h ≤ |c-b| ∧ Q c⊆F ∧
        q*(F.card:ℝ) ≤ (Q c).card ∧ cover c (Q c) ≤ M := by
  let B := bad C F q M cover
  let D := awayTwo B a b h
  have hBC : B⊆C := original_bad_subset C F q M cover
  have hDB : D⊆B := Finset.filter_subset _ _
  have hBmass := hfailure F hFP hFmass
  have hcap (z : ℝ) : ((C.filter (fun c => |c-z| ≤ h)).card:ℝ) ≤
      (beta/4)*C.card := (hprofile z h hscale hh1).trans
        (mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg _))
  have hdel := away_two_card C B a b h ((beta/4)*C.card) hBC (hcap a) (hcap b)
  have hmass : (beta/2)*(C.card:ℝ) ≤ D.card := by nlinarith only [hBmass,hdel]
  have hD : D.Nonempty := by
    have hp : (0:ℝ) < D.card := (mul_pos (by positivity : 0<beta/2)
      (Nat.cast_pos.mpr hC.card_pos)).trans_le hmass
    exact Finset.card_pos.mp (Nat.cast_pos.mp hp)
  have hprof : ScalarFrostman D delta (2*K/beta) u := by
    have hm : (1-(1-beta/2))*(C.card:ℝ) ≤ D.card := by nlinarith only [hmass]
    have hh := original_slope_profile_restrict C D (hDB.trans hBC) hd
      (show 1-beta/2<1 by linarith only [hbeta]) hK hm hprofile
    have he : K/(1-(1-beta/2))=2*K/beta := by
      rw [show (1:ℝ)-(1-beta/2)=beta/2 by ring]
      field_simp
    rw [he] at hh
    exact hh
  obtain ⟨Q,hQ⟩ := exists_original_bad_query_family C F q M cover
  refine ⟨D,hDB.trans hBC,hD,hmass,hprof,Q,?_⟩
  intro c hc
  obtain ⟨hca,hcb⟩ := (Finset.mem_filter.mp hc).2
  exact ⟨hca,hcb,hQ c (hDB hc)⟩

/-- Negating the explicit failure predicate constructs the actual local
robust conclusion, with its original source and coefficient populations. -/
theorem local_robust_of_not_failure (P : Finset X) (C : Finset ℝ)
    (mass q beta M : ℝ) (cover : ℝ → Finset X → ℝ)
    (hnot : ¬Failure P C mass q beta M cover) :
    ∃ F : Finset X, F⊆P ∧ mass*(P.card:ℝ) ≤ F.card ∧
      ∃ Good : Finset ℝ, Good⊆C ∧ (1-beta)*(C.card:ℝ) < Good.card ∧
        ∀ c∈Good, ∀ Q : Finset X, Q⊆F → q*(F.card:ℝ) ≤ Q.card → M < cover c Q := by
  unfold Failure at hnot
  push Not at hnot
  obtain ⟨F,hFP,hFmass,hbad⟩ := hnot
  let Good := C \ bad C F q M cover
  have hsubset := original_bad_subset C F q M cover
  have hcard : (Good.card:ℝ)+(bad C F q M cover).card=C.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hsubset
  refine ⟨F,hFP,hFmass,Good,Finset.sdiff_subset,?_,?_⟩
  · nlinarith only [hcard,hbad]
  · intro c hc Q hQ hmass
    have hcC := (Finset.mem_sdiff.mp hc).1
    have hcnot := (Finset.mem_sdiff.mp hc).2
    by_contra h
    exact hcnot (Finset.mem_filter.mpr ⟨hcC,Q,hQ,hmass,le_of_not_gt h⟩)

end OriginalFreshProjectionQueries
